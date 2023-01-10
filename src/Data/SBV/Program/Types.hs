{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.SBV.Program.Types (
  module Data.Biapplicative,
  module Data.Bifoldable,
  module Data.Bitraversable,

  Location,
  SLocation,

  SynthSpec(..),
  SynthComponent(..),

  SimpleSpec(..),
  SimpleComponent(..),

  SynthesisError(..),

  IOs(..),
  Instruction(..),
  Program(..),
  toIOsList,
  sortInstructions,

  ProgramTree(..),
  buildProgramTree,
  buildForestResult,
  )
where

import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.SBV


-- | Type used to represent a value from the __set of location variables__ \(l_x \in L\).
type Location = Word64
-- | Symbolic 'Location'.
type SLocation = SWord64


-- | Class for a program or a component __specification__ \(φ(\vec I, O)\). Type
-- variable 'a' stands for function's domain type.
class SynthSpec s a where
  -- | Number of inputs the specification function takes.
  specArity :: s a -> Word
  -- | An equation that relates input variables to the output one. The equation is
  -- build up either using '(.==)' or in a "tabular" way using multiple '(.=>)'
  -- expressions. See definitions from the Data.SBV.Program.SimpleLibrary module
  -- for examples.
  specFunc :: s a
    -- | Input variables. The list should be of 'specArity' size.
    -> [SBV a]
    -- | Output variable.
    -> SBV a
    -> SBool

-- | A class for a __library component__.
class SynthSpec spec a => SynthComponent comp spec a | comp -> spec where
  -- | Component name (optional). Used for naming SBV variables and when rendering the resulting program.
  compName :: comp a -> String
  -- | Component's __specification__.
  compSpec :: comp a -> spec a
  -- | Optional constraints to set on __location variables__ \(l_x \in L\).
  extraLocConstrs :: comp a -> [[SLocation] -> SLocation -> SBool]

  compName = const ""
  extraLocConstrs = const []


-- | A simplest __specification__ datatype possible. Type variable 'a' stands
-- for function's domain type.
data SimpleSpec a = SimpleSpec {
    simpleArity :: Word
  , simpleFunc :: [SBV a] -> SBV a -> SBool
  }

instance SynthSpec SimpleSpec a where
  specArity = simpleArity
  specFunc = simpleFunc

-- | A simplest __library component__ datatype possible.
data SimpleComponent a = SimpleComponent {
    simpleName :: String
  , simpleSpec :: SimpleSpec a
  }

instance SynthComponent SimpleComponent SimpleSpec a where
  compName = simpleName
  compSpec = simpleSpec
  extraLocConstrs = const []

instance Show (SimpleComponent spec) where
  show = compName


-- | Possible failure reasons during synthesis operation.
data SynthesisError = ErrorUnsat
                    | ErrorUnknown String
                    | ErrorZeroResultsRequested
                    | ErrorSeedingFailed
  deriving Show


-- | A datatype holding inputs and output of something. Usual types for 'l' are 'Location' and 'SLocation'.
data IOs l = IOs {
    _ins :: [l],
    _out :: l
  }
  deriving (Show, Eq, Ord, Functor)

instance Foldable IOs where
  foldMap f (IOs {..}) = mconcat (map f _ins) `mappend` f _out

instance Traversable IOs where
  traverse f (IOs {..}) = IOs <$> traverse f _ins <*> f _out

instance EqSymbolic l => EqSymbolic (IOs l) where
  l .== r = toList l .== toList r


-- | A datatype that holds a 'SynthComponent' with inputs and output locations.
data Instruction l a = Instruction {
    instructionIOs :: IOs l,
    instructionComponent :: a
  }
  deriving (Show, Eq, Ord)

instance Bifunctor Instruction where
  bimap iosF compF (Instruction {..}) = Instruction (fmap iosF instructionIOs) (compF instructionComponent)

instance Bitraversable Instruction where
  bitraverse iosF compF (Instruction ios comp) = Instruction <$> traverse iosF ios <*> compF comp

instance Bifoldable Instruction where
  bifoldMap f1 f2 (Instruction {..}) = foldMap f1 instructionIOs `mappend` f2 instructionComponent


-- | A datatype that unites program instructions with 'IOs' of the program itself.
data Program l a = Program {
    programIOs :: IOs l,
    programInstructions :: [Instruction l a]
  }
  deriving (Show, Eq, Ord)

instance Bifunctor Program where
  bimap iosF compF (Program {..}) = Program (fmap iosF programIOs) (map (bimap iosF compF) programInstructions)

instance Bitraversable Program where
  bitraverse iosF compF (Program ios instrs) = Program <$> traverse iosF ios <*> traverse (bitraverse iosF compF) instrs

instance Bifoldable Program where
  bifoldMap f1 f2 (Program {..}) = foldMap f1 programIOs `mappend` foldMap (bifoldMap f1 f2) programInstructions

-- | Extract all locations from the program as a list, including locations of instructions.
toIOsList :: Program l a -> [l]
toIOsList = bifoldMap (:[]) (const mempty)

-- | Sorts program's instructions by their output location.
sortInstructions :: Ord l => Program l a -> Program l a
sortInstructions p = p { programInstructions = sortOn (_out . instructionIOs) (programInstructions p) }


-- | A `Program` converted into a tree-like structure.
data ProgramTree a = InstructionNode a [ProgramTree a]
                   | InputLeaf Location
    deriving (Show, Eq, Ord, Functor)

instance Foldable ProgramTree where
  foldMap _ (InputLeaf _) = mempty
  foldMap f (InstructionNode comp children) = foldMap (foldMap f) children <> f comp

-- | Create a 'ProgramTree' for a given 'Program' by resolving its 'Location's.
-- This function effectively performs dead code elimination.
buildProgramTree :: Program Location a -> ProgramTree a
buildProgramTree prog = buildProgramTree' prog (_out $ programIOs prog)

-- | A variant of 'buildProgramTree' that builds from a specified starting point.
buildProgramTree' :: Program Location a -> Location -> ProgramTree a
buildProgramTree' prog@(Program {..}) startingOutputLoc =
  if startingOutputLoc `notElem` _ins programIOs
    then InstructionNode
        (instructionComponent (instsMap M.! startingOutputLoc))
        (map (buildProgramTree' prog) $ _ins $ instructionIOs (instsMap M.! startingOutputLoc))
    else InputLeaf startingOutputLoc
  where
    instsMap = M.fromList $ map (\inst -> (_out $ instructionIOs inst, inst)) programInstructions

-- | Create a 'ProgramTree' for each unused output in the 'Program'
buildForestResult sr@(Program {..}) = map (buildProgramTree' sr) rootOutputs
  where
    inputsSet = S.fromList $ _ins programIOs ++ concatMap (_ins . instructionIOs) programInstructions
    rootOutputs = filter isRootOutput $ map (_out . instructionIOs) programInstructions
    isRootOutput o = o `S.notMember` inputsSet
