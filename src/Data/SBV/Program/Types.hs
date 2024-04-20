{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.SBV.Program.Types (
    --  module Data.Biapplicative,
    module Data.Bifoldable,
    module Data.Bitraversable,
    Location,
    SLocation,
    SynthSpec (..),
    SynthComponent (..),
    SimpleSpec (..),
    SimpleComponent (..),
    mkSimpleComp,
    SynthesisError (..),
    IOs (..),
    Instruction (..),
    Program (..),
    toIOsList,
    sortInstructions,
    ProgramTree (..),
    buildProgramTree,
    buildForestResult,

    -- * Addendum
    programToHaskell,
    requestValueNames,
) where

-- import Data.Biapplicative

import Control.Monad (replicateM)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Ix qualified as Ix
import Data.List
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map (Map)
import Data.Map qualified as Map
import Data.SBV
import Data.Semigroup (Arg (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector (Vector)
import Data.Vector qualified as Vec


-- | Type used to represent a value from the __set of location variables__ \(l_x \in L\).
type Location = Word64


-- | Symbolic 'Location'.
type SLocation = SWord64


{- | Class for a program or a component __specification__ \(φ(\vec I, O)\). Type
variable 'a' stands for function's domain type.
-}
class SynthSpec s a where
    -- | Number of inputs the specification function takes.
    specArity ∷ s a → Word


    -- | An equation that relates input variables to the output one. The equation is
    -- build up either using '(.==)' or in a "tabular" way using multiple '(.=>)'
    -- expressions. See definitions from the Data.SBV.Program.SimpleLibrary module
    -- for examples.
    specFunc
        ∷ s a
        → [SBV a]
        -- ^ Input variables. The list should be of 'specArity' size.
        → SBV a
        -- ^ Output variable.
        → SBool


-- | A class for a __library component__.
class (SynthSpec spec a) ⇒ SynthComponent comp spec a | comp → spec where
    -- | Component name (optional). Used for naming SBV variables and when rendering the resulting program.
    compName ∷ comp a → String


    -- | Component's __specification__.
    compSpec ∷ comp a → spec a


    -- | Optional constraints to set on __location variables__ \(l_x \in L\).
    extraLocConstrs ∷ comp a → [[SLocation] → SLocation → SBool]


    -- | Method used to get the value of a constant component. It doesn't require
    -- an implementation if you don't use constant components.
    getConstValue ∷ comp a → a


    -- | Method used to by the synthesis procedure to set the value of a constant
    -- component. It doesn't require an implementation if you don't use constant
    -- components.
    putConstValue ∷ comp a → a → comp a


    compName = const ""
    extraLocConstrs = const []
    getConstValue = const undefined
    putConstValue = const


{- | A simplest __specification__ datatype possible. Type variable 'a' stands
for function's domain type.
-}
data SimpleSpec a = SimpleSpec
    { simpleArity ∷ Word
    , simpleFunc ∷ [SBV a] → SBV a → SBool
    }


instance SynthSpec SimpleSpec a where
    specArity = simpleArity
    specFunc = simpleFunc


-- | A simplest __library component__ datatype possible.
data SimpleComponent a = SimpleComponent
    { simpleName ∷ String
    , simpleSpec ∷ SimpleSpec a
    , simpleVal ∷ a
    }


mkSimpleComp name spec =
    SimpleComponent
        { simpleName = name
        , simpleSpec = spec
        , simpleVal = undefined
        }


instance SynthComponent SimpleComponent SimpleSpec a where
    compName = simpleName
    compSpec = simpleSpec
    extraLocConstrs = const []
    getConstValue = simpleVal
    putConstValue comp c = comp{simpleVal = c}


instance Show (SimpleComponent spec) where
    show = compName


-- | Possible failure reasons during synthesis operation.
data SynthesisError
    = ErrorUnsat
    | ErrorUnknown String
    | ErrorZeroResultsRequested
    | ErrorSeedingFailed
    deriving (Show)


-- | A datatype holding inputs and output of something. Usual types for 'l' are 'Location' and 'SLocation'.
data IOs l = IOs
    { _ins ∷ [l]
    , _out ∷ l
    }
    deriving (Show, Eq, Ord, Functor)


instance Foldable IOs where
    foldMap f (IOs{..}) = mconcat (map f _ins) `mappend` f _out


instance Traversable IOs where
    traverse f (IOs{..}) = IOs <$> traverse f _ins <*> f _out


instance (EqSymbolic l) ⇒ EqSymbolic (IOs l) where
    l .== r = toList l .== toList r


-- | A datatype that holds a 'SynthComponent' with inputs and output locations.
data Instruction l a = Instruction
    { instructionIOs ∷ IOs l
    , instructionComponent ∷ a
    }
    deriving (Show, Eq, Ord)


instance Functor (Instruction l) where
    fmap compF (Instruction{..}) = Instruction instructionIOs (compF instructionComponent)


instance Bifunctor Instruction where
    bimap iosF compF (Instruction{..}) = Instruction (fmap iosF instructionIOs) (compF instructionComponent)


instance Bitraversable Instruction where
    bitraverse iosF compF (Instruction ios comp) = Instruction <$> traverse iosF ios <*> compF comp


instance Bifoldable Instruction where
    bifoldMap f1 f2 (Instruction{..}) = foldMap f1 instructionIOs `mappend` f2 instructionComponent


-- | A datatype that unites program instructions with 'IOs' of the program itself.
data Program l a = Program
    { programIOs ∷ IOs l
    , programInstructions ∷ NonEmpty (Instruction l a)
    }
    deriving (Show, Eq, Ord)


instance Functor (Program l) where
    fmap compF (Program{..}) = Program programIOs $ fmap compF <$> programInstructions


instance Bifunctor Program where
    bimap iosF compF (Program{..}) = Program (fmap iosF programIOs) $ bimap iosF compF <$> programInstructions


instance Bitraversable Program where
    bitraverse iosF compF (Program ios instrs) = Program <$> traverse iosF ios <*> traverse (bitraverse iosF compF) instrs


instance Bifoldable Program where
    bifoldMap f1 f2 (Program{..}) = foldMap f1 programIOs `mappend` foldMap (bifoldMap f1 f2) programInstructions


-- | Extract all locations from the program as a list, including locations of instructions.
toIOsList ∷ Program l a → [l]
toIOsList = bifoldMap (: []) (const mempty)


-- | Sorts program's instructions by their output location.
sortInstructions ∷ (Ord l) ⇒ Program l a → Program l a
sortInstructions p = p{programInstructions = NE.sortWith (_out . instructionIOs) (programInstructions p)}


-- | A `Program` converted into a tree-like structure.
data ProgramTree a
    = InstructionNode a [ProgramTree a]
    | InputLeaf Location
    deriving (Show, Eq, Ord, Functor)


instance Foldable ProgramTree where
    foldMap _ (InputLeaf _) = mempty
    foldMap f (InstructionNode comp children) = foldMap (foldMap f) children <> f comp


{- | Create a 'ProgramTree' for a given 'Program' by resolving its 'Location's.
This function effectively performs dead code elimination.
-}
buildProgramTree ∷ Program Location a → ProgramTree a
buildProgramTree prog = buildProgramTree' prog (_out $ programIOs prog)


-- | A variant of 'buildProgramTree' that builds from a specified starting point.
buildProgramTree' ∷ Program Location a → Location → ProgramTree a
buildProgramTree' prog@(Program{..}) startingOutputLoc =
    if startingOutputLoc `notElem` _ins programIOs
        then
            InstructionNode
                (instructionComponent (instsMap Map.! startingOutputLoc))
                (map (buildProgramTree' prog) $ _ins $ instructionIOs (instsMap Map.! startingOutputLoc))
        else InputLeaf startingOutputLoc
    where
        transform inst = (_out $ instructionIOs inst, inst)
        instsMap = Map.fromList . toList $ transform <$> programInstructions


-- | Create a 'ProgramTree' for each unused output in the 'Program'
buildForestResult sr@(Program{..}) = map (buildProgramTree' sr) rootOutputs
    where
        inputsSet = Set.fromList $ _ins programIOs ++ concatMap (_ins . instructionIOs) programInstructions
        rootOutputs = NE.filter isRootOutput $ _out . instructionIOs <$> programInstructions
        isRootOutput o = o `Set.notMember` inputsSet


-- TODO use Template Haskell to directly encode AST

{- |
Serialize a 'Program' to a Haskell-like functional program.
-}
programToHaskell ∷ ∀ a l. (Enum l, Show a, Show l) ⇒ Program l a → String
programToHaskell (Program (IOs iParams oParam) progLines) =
    let valueNames ∷ Vector String
        valueNames = requestValueNames valueCount

        valueCount ∷ Word
        valueCount =
            let lo = case fromEnum <$> iParams of
                    [] → 0
                    x : xs → minimum $ x :| xs
            in  toEnum $ Ix.rangeSize (lo, fromEnum oParam)

        getValueName ∷ l → String
        getValueName = Vec.unsafeIndex valueNames . fromEnum

        renderBinding ∷ Instruction l a → Map String String
        renderBinding (Instruction (IOs iRefs oRef) cName) =
            let iNames = getValueName <$> iRefs
                oName = getValueName oRef
            in  Map.singleton oName $ unwords $ ["=", show cName] <> iNames

        renderedLineBindings ∷ Map String String
        renderedLineBindings = foldMap renderBinding progLines

        renderLine ∷ String → String → [String]
        renderLine strName strExpr = [unwords [strName, strExpr]]

        renderedLines ∷ [String]
        renderedLines = ("    " <>) <$> Map.foldMapWithKey renderLine renderedLineBindings
    in  unlines $ "let " : renderedLines <> ["in  " <> getValueName oParam]


{- |
Generate the specified number of unique value names.
-}
requestValueNames ∷ Word → Vector String
requestValueNames n =
    let i = fromEnum n
    in  Vec.fromListN i $ NE.take i progVariableNameStream


{- |
An infinite stream of base-36 encoded varaiable names.
-}
progVariableNameStream ∷ NonEmpty String
progVariableNameStream =
    let infNums ∷ NonEmpty Int
        infNums = 1 :| [2 ..]

        base36 ∷ NonEmpty Char
        base36 = '0' :| ['1' .. '9'] <> ['A' .. 'Z']

        baseVals ∷ NonEmpty String
        baseVals = infNums >>= (`replicateM` base36)
    in  ('v' :) <$> baseVals
