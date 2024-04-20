{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
--
{-# LANGUAGE ScopedTypeVariables #-}

{- | This module implements an algorithm described in the
"Component-based Synthesis Applied to Bitvector Programs" paper.

https://www.microsoft.com/en-us/research/wp-content/uploads/2010/02/bv.pdf

Given a program specification along with a library of available components
it synthesizes an actual program using an off-the-shelf SMT-solver.

The specification is an arbitrary datatype that is an instance of the 'SynthSpec' class.
The library is a list of 'SynthComponent' instances.

There are three entry points to this module: 'standardExAllProcedure', 'refinedExAllProcedure' and 'exAllProcedure'.
-}
module Data.SBV.Program (
    -- * Definitions for specification and component classes and the resulting data type
    module Data.SBV.Program.Types,

    -- * Predefined components library
    module Data.SBV.Program.SimpleLibrary,

    -- * Various utility functions
    module Data.SBV.Program.Utils,

    -- * Package entry points #entry#
    standardExAllProcedure,
    refinedExAllProcedure,
    exAllProcedure,
    standardExAllProcedureWith,
    refinedExAllProcedureWith,
    exAllProcedureWith,

    -- * Auxiliary functions that make up synthesis procedures #aux#
    createProgramLocs,
    constrainLocs,
    createProgramVarsWith,
    createVarsConstraints,

    -- * Constant components handling #constants#
    createConstantVars,
    combineProgramVars,
    instructionGetValue,
) where

import Control.Monad
import Control.Monad.IO.Class
import Data.Either
import Data.Foldable
import Data.Functor ((<&>))
import Data.List
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe
import Data.Ord (comparing)
import Data.SBV hiding (STuple)
import Data.SBV.Control
import Data.SBV.Program.SimpleLibrary
import Data.SBV.Program.Types
import Data.SBV.Program.Utils
import Data.Traversable (for)
import Text.Pretty.Simple (pPrint)


{- | Represents a failed run in 'standardExAllProcedure'. Corresponds to
__program variable__ \(S\) in the paper.
-}
data STuple a = STuple
    { s_ios ∷ IOs a
    , s_comps ∷ [IOs a]
    }
    deriving (Show)


{- | An implementation of __StandardExAllSolver__ presented in section 6.1 of the paper.
As stated in the paper, this implementation boils down to exhaustive enumeration
of possible solutions, and as such isn't effective. It can be used to better
understand how the synthesis procedure works and provides a lot of debugging
output. It also doesn't support constant components. Do not use this procedure
for solving real problems.
-}
standardExAllProcedure
    ∷ ∀ a comp spec
     . (SymVal a, Show a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ NonEmpty (comp a)
    -- ^ Component library
    → spec a
    -- ^ Specification of program being synthesized
    → IO (Either SynthesisError (Program Location (comp a)))
standardExAllProcedure = standardExAllProcedureWith defaultSMTCfg


-- | Version of 'standardExAllProcedure' that uses passed 'SMTConfig' instead of default one.
standardExAllProcedureWith
    ∷ ∀ a comp spec
     . (SymVal a, Show a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ SMTConfig
    → NonEmpty (comp a)
    -- ^ Component library
    → spec a
    -- ^ Specification of program being synthesized
    → IO (Either SynthesisError (Program Location (comp a)))
standardExAllProcedureWith config library spec = do
    -- generate a seed for S
    mbRes ← sampleSpec spec
    case mbRes of
        Nothing → return $ Left ErrorSeedingFailed
        Just i0 → do
            putStrLn "Seeding done, result:"
            print i0
            go 1 [STuple (i0 ∷ IOs a) []]
    where
        n = genericLength' library
        numInputs = specArity spec
        m = n + numInputs
        go step s = do
            putStrLn "============="
            putStrLn "Synthesizing with s = "
            pPrint s
            -- Finite synthesis part
            r ← runSMTWith config $ do
                progLocs ← createProgramLocs library numInputs

                constrainLocs m numInputs progLocs

                -- Unlike 'exAllProcedure' we call 'createProgramVarsWith' here multiple times
                -- Since we aren't using forall quantifier, we have to create variables
                -- for each STuple item in s.
                manyProgVars ← forM s $ \(STuple{..}) → do
                    let numInputs = genericLength' $ _ins s_ios
                    progVars ← createProgramVarsWith free library numInputs

                    -- pin input/output variables (members of I and O sets) to values from S
                    constrain $ fmap literal s_ios .== programIOs progVars
                    -- on the first run we don't have values for component locations (members of T set in the paper)
                    case s_comps of
                        [] → pure ()
                        x : xs →
                            constrain $
                                fmap (fmap literal) (x :| xs) .== fmap instructionIOs (programInstructions progVars)

                    return progVars

                forM_ manyProgVars $ \progVars → do
                    let (IOs inputVars outputVar) = programIOs progVars
                        (psi_conn, phi_lib) = createVarsConstraints progLocs progVars
                    constrain $ (phi_lib .&& psi_conn) .=> specFunc spec inputVars outputVar

                query $ do
                    r ← checkSat
                    case r of
                        Sat → do
                            solution ← mapM getValue (programIOs progLocs)
                            componentLocVals ← traverse (bimapM getValue pure) (programInstructions progLocs)
                            return $ Right (Program solution componentLocVals)
                        Unsat → return $ Left ErrorUnsat
                        Unk → Left . ErrorUnknown . show <$> getUnknownReason
            -- Verification part
            -- At this stage the 'currL' program represents a solution that is known to
            -- work for all values from S. We now check if this solution works for all
            -- values possible.
            fmap join $ for r $ \currL → runSMTWith config $ do
                liftIO $ do
                    putStrLn "Synthesis step done, current solution:"
                    putStrLn $ writePseudocode currL

                progLocs ← createProgramLocs library numInputs

                -- In the verification part we pin location variables L
                constrain $ (literal <$> programIOs currL) .== programIOs progLocs
                constrain $
                    sAnd $
                        zipWith
                            (\x y → literal x .== y)
                            (concatMap (toList . instructionIOs) (programInstructions currL))
                            (concatMap (toList . instructionIOs) (programInstructions progLocs))

                progVars ← createProgramVarsWith free library numInputs

                let Program (IOs inputVars outputVar) componentVars = progVars
                    (psi_conn, phi_lib) = createVarsConstraints progLocs progVars

                constrain $ sNot $ (phi_lib .&& psi_conn) .=> specFunc spec inputVars outputVar

                query $ do
                    r ← checkSat
                    io $ putStrLn "Verification step done"
                    case r of
                        Unsat → do
                            io $ do
                                putStrLn "============="
                                putStrLn ("Solution found after " ++ show step ++ " iterations")
                            return $ Right currL
                        Sat → do
                            io $ putStrLn "Solution does not work for all inputs"
                            inputVals ← mapM getValue inputVars
                            outputVal ← getValue outputVar
                            componentVals ← mapM (traverse getValue . instructionIOs) componentVars
                            io $ go (step + 1) $ STuple (IOs inputVals outputVal) (toList componentVals) : s


{- | An implementation of __RefinedExAllSolver__ presented in section 6.2 of the paper.
This is an improved version of 'standardExAllProcedure'. It only keeps input
values \(|\vec I|\) in \(S\) and uses different synthesis constraints on __synthesis__
and __verification__ steps.
-}
refinedExAllProcedure
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ NonEmpty (comp a)
    -- ^ Component library
    → spec a
    -- ^ Specification of program being synthesized
    → IO (Either SynthesisError (Program Location (comp a)))
refinedExAllProcedure = refinedExAllProcedureWith defaultSMTCfg


-- | Version of 'refinedExAllProcedure' that uses passed 'SMTConfig' instead of default one.
refinedExAllProcedureWith
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ SMTConfig
    → NonEmpty (comp a)
    -- ^ Component library
    → spec a
    -- ^ Specification of program being synthesized
    → IO (Either SynthesisError (Program Location (comp a)))
refinedExAllProcedureWith config library spec = do
    mbRes ← sampleSpec spec
    case mbRes of
        Nothing → return $ Left ErrorSeedingFailed
        Just r → go ([_ins r] ∷ [[a]])
    where
        n = genericLength' library
        numInputs = specArity spec
        m = n + numInputs
        go s = do
            -- Finite synthesis part
            r ← runSMTWith config $ do
                progLocs ← createProgramLocs library numInputs

                constrainLocs m numInputs progLocs

                -- Not part of the original paper.
                -- Here we create existentially quantified variables for constant components.
                -- These variables represent actual value that the component returns.
                -- The returned 'Program' is filled with 'undefined' values for non-constant
                -- components.
                progConsts ← createConstantVars library

                -- Unlike 'exAllProcedure' here we call 'createProgramVarsWith' multiple times.
                -- Since we aren't using forall quantifier, we have to create variables
                -- for each I vector in s.
                manyProgVars ← forM s $ \inputVars_s → do
                    let numInputs = genericLength' inputVars_s
                    progVars0 ← createProgramVarsWith free library numInputs

                    -- Not part of the original paper.
                    -- Combine variables of constant components with variable of non-constant ones.
                    -- The resulting program will not contain 'undefined' values anymore.
                    let progVars = combineProgramVars progConsts progVars0

                    -- pin input variables (members of I set) to values from S
                    constrain $ fmap literal inputVars_s .== _ins (programIOs progVars)

                    return progVars

                forM_ manyProgVars $ \progVars → do
                    let (IOs inputVars outputVar) = programIOs progVars
                        (psi_conn, phi_lib) = createVarsConstraints progLocs progVars
                    constrain $ (phi_lib .&& psi_conn) .&& specFunc spec inputVars outputVar

                query $ do
                    r ← checkSat
                    case r of
                        Sat → do
                            -- We could've just call 'bimapM getValue pure' to get all solutions
                            -- at once, but in presence of constant components we have to do
                            -- a bit more manual work.
                            inputLocVals ← mapM getValue (_ins $ programIOs progLocs)
                            outputLocVal ← getValue (_out $ programIOs progLocs)
                            -- Carefully extract solutions for component location vars.
                            -- The 'instructionGetValue' function selectively calls 'getValue'
                            -- either on left-hand 'Program' or right-hand 'Program' depending
                            -- on component's constness.
                            componentLocVals ← zipWithNEM instructionGetValue (programInstructions progLocs) (programInstructions progConsts)
                            constantVals ←
                                mapM
                                    (getValue . _out . instructionIOs)
                                    (NE.filter (isConstantComponent . instructionComponent) (programInstructions progConsts))

                            let currL = Program (IOs inputLocVals outputLocVal) componentLocVals
                            return $ Right (currL, constantVals)
                        _ → return $ Left ErrorUnsat
            -- Verification part
            -- At this stage the 'currL' program represents a solution that is known to
            -- work for all values from S. We now check if this solution works for all
            -- values possible.
            fmap join $ for r $ \(currL, constantVals) → runSMTWith config $ do
                progLocs ← createProgramLocs library numInputs

                -- In the verification part we pin location variables L
                constrain $ (literal <$> programIOs currL) .== programIOs progLocs
                constrain $
                    sAnd $
                        zipWith
                            (\x y → literal x .== y)
                            (concatMap (toList . instructionIOs) (programInstructions currL))
                            (concatMap (toList . instructionIOs) (programInstructions progLocs))

                -- For constant components we also pin their return values.
                progConsts ← createConstantVars library
                constrain $
                    fmap (_out . instructionIOs) (NE.filter (isConstantComponent . instructionComponent) (programInstructions progConsts))
                        .== fmap literal constantVals

                -- We want to find at least one set of inputs that doesn't work for our
                -- current design, hence existential quantification.
                progVars0 ← createProgramVarsWith free library numInputs
                let progVars = combineProgramVars progConsts progVars0

                let (Program (IOs inputVars outputVar) componentVars) = progVars
                    (psi_conn, phi_lib) = createVarsConstraints progLocs progVars

                constrain $ (phi_lib .&& psi_conn) .&& sNot (specFunc spec inputVars outputVar)

                query $ do
                    r ← checkSat
                    case r of
                        -- We were unable to find any counterexamples, which means that
                        -- our design works for all inputs. Return it.
                        Unsat → return $ Right currL
                        -- We found a set of input assignments that makes our design return
                        -- wrong values. Add this set to 's' and go to the next iteration.
                        Sat → do
                            inputVals ← mapM getValue inputVars
                            io $ go $ inputVals : s


{- | This procedure is not part of the paper. It uses forall quantification directly
when creating variables from the \(T\) set. As consequence it requires an SMT-solver
than can handle foralls (for instance, Z3). This procedure is the easiest to
understand.
-}
exAllProcedure
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ NonEmpty (comp a)
    -- ^ Component library
    → spec a
    -- ^ Specification of program being synthesized
    → IO (Either SynthesisError (Program Location (comp a)))
exAllProcedure = exAllProcedureWith defaultSMTCfg


-- | Version of 'exAllProcedure' that uses passed 'SMTConfig' instead of default one.
exAllProcedureWith
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ SMTConfig
    → NonEmpty (comp a)
    -- ^ Component library
    → spec a
    -- ^ Specification of program being synthesized
    → IO (Either SynthesisError (Program Location (comp a)))
exAllProcedureWith config library spec =
    -- run SBV with 'allowQuantifiedQueries' to silence warnings about entering
    -- 'query' mode in presence of universally quantified variables
    --  runSMTWith (config {allowQuantifiedQueries = True}) $ do
    runSMTWith config $ do
        let n = genericLength' library
            numInputs = specArity spec
            m = n + numInputs

        progLocs ← createProgramLocs library numInputs

        constrainLocs m numInputs progLocs

        -- Not part of the original paper. See comments for the similar call in 'refinedExAllProcedure'.
        progConsts ← createConstantVars library

        --    important ForAll universal quantificatioon constraint
        --    progVars0 <- createProgramVarsWith sbvForall library numInputs
        progVars0 ← createProgramVarsWith free library numInputs
        let progVars = combineProgramVars progConsts progVars0

        let (Program (IOs inputVars outputVar) _) = progVars
            (psi_conn, phi_lib) = createVarsConstraints progLocs progVars

        constrain $ (phi_lib .&& psi_conn) .=> specFunc spec inputVars outputVar

        query $ do
            r ← checkSat
            case r of
                Sat → do
                    inputLocVals ← mapM getValue (_ins $ programIOs progLocs)
                    outputLocVal ← getValue (_out $ programIOs progLocs)
                    -- Careful solution extraction. See comments for the similar call in 'refinedExAllProcedure'.
                    componentLocVals ← zipWithNEM instructionGetValue (programInstructions progLocs) (programInstructions progConsts)
                    return $ Right $ Program (IOs inputLocVals outputLocVal) componentLocVals
                Unsat → return $ Left ErrorUnsat
                Unk → do
                    reason ← getUnknownReason
                    return $ Left $ ErrorUnknown $ "Unknown: " ++ show reason


{- | First step of each synthesis procedure. Given a library of components and
a number of program's inputs, it creates existentially quantified
__location variables__ (members of set \(L\) in the paper) for each component
and for the program itself.
-}
createProgramLocs
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ NonEmpty (comp a)
    → Word
    → Symbolic (Program SLocation (comp a))
createProgramLocs library numInputs = do
    inputLocs ← mapM free $ genericTake numInputs ["InputLoc" ++ show i | i ← [1 ..]] ∷ Symbolic [SLocation]
    outputLoc ← free "OutputLoc" ∷ Symbolic SLocation

    componentsWithLocs ← forM library $ \component → do
        let n' = specArity $ compSpec component
        compInputLocs ← mapM free $ genericTake n' [mkInputLocName (compName component) i | i ← [1 ..]]
        compOutputLoc ← free $ mkOutputLocName $ compName component
        return $ Instruction (IOs compInputLocs compOutputLoc) component ∷ Symbolic (Instruction SLocation (comp a))

    pure $ Program (IOs inputLocs outputLoc) componentsWithLocs


{- | Second step of each synthesis procedure. It applies constraints on
__location variables__ from section 5 of the original paper. These constraints
include __well-formedness constraint__ \(ψ_{wfp}\), __acyclicity constraint__
\(ψ_{acyc}\) and __consistency constraint__ \(ψ_{cons}\). Constraints are not
returned from this function, but are applied immediately. Section 5 of the
paper also talks about __connectivity constraint__ \(ψ_{conn}\), which is
not created here.
-}
constrainLocs
    ∷ (SynthSpec spec a, SynthComponent comp spec a)
    ⇒ Word
    -- ^ The \(M\) constant from the paper, which equals to \(N + |\vec I|\), where
    -- __N__ is the size of the library.
    → Word
    -- ^ Number of program inputs \(|\vec I|\).
    → Program SLocation (comp a)
    → Symbolic ()
constrainLocs m numInputs (Program{..}) = do
    -- program inputs are assigned locations from 0 to numInputs
    forM_ (zip [0 ..] (_ins programIOs)) $ \(i, inputLoc) → do
        constrain $ inputLoc .== literal i
    -- program output location should not be greater than the number of instructions
    constrain $ _out programIOs .< fromIntegral m

    forM_ programInstructions $ \(Instruction (IOs compInputLocs compOutputLoc) comp) → do
        forM_ compInputLocs $ \inputLoc → do
            -- psi_wfp for component inputs
            constrain $ inputLoc .>= literal 0
            constrain $ inputLoc .<= literal (fromIntegral $ m - 1)
            -- psi_acyc
            constrain $ inputLoc .< compOutputLoc

        -- psi_wfp for component outputs
        constrain $ compOutputLoc .>= literal (fromIntegral numInputs)
        constrain $ compOutputLoc .<= literal (fromIntegral $ m - 1)

        -- extra constraints supplied by user
        forM_ (extraLocConstrs comp) $ \extraConstr →
            constrain $ extraConstr compInputLocs compOutputLoc

    -- psi_cons
    constrain . distinct . toList $ _out . instructionIOs <$> programInstructions


{- | Third step of the synthesis process. It creates variables that represent
actual inputs/outputs values (members of the set \(T\) in the paper). This
function resembles 'createProgramLocs', but unlike it allows creating both existentially
and universally quantified variables. Standard and Refined procedures pass
'free' to create existentially quantified variables, while 'exAllProcedure'
uses 'sbvForall'.
-}
createProgramVarsWith
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ (String → Symbolic (SBV a))
    -- ^ Variable creation function. Either 'free' or 'sbvForall'.
    → NonEmpty (comp a)
    -- ^ Component library.
    → Word
    -- ^ Number of program inputs \(|\vec I|\).
    → Symbolic (Program (SBV a) (comp a))
createProgramVarsWith sbvMakeFunc library numInputs = do
    inputVars ← mapM sbvMakeFunc $ genericTake numInputs ["Input" ++ show i | i ← [1 ..]]
    outputVar ← sbvMakeFunc "Output"

    componentVars ← forM library $ \comp → do
        let n' = specArity $ compSpec comp
        compInputVars ← mapM sbvMakeFunc $ genericTake n' [mkInputVarName (compName comp) i | i ← [1 ..]]
        compOutputVar ← sbvMakeFunc $ mkOutputVarName $ compName comp
        return $ Instruction (IOs compInputVars compOutputVar) comp

    return $ Program (IOs inputVars outputVar) componentVars


{- | Last building block of the synthesis process. This function creates
\(ψ_{conn}\) and \(φ_{lib}\) constraints and return them.
-}
createVarsConstraints ∷ (SynthComponent comp spec a) ⇒ Program SLocation (comp a) → Program (SBV a) (comp a) → (SBool, SBool)
createVarsConstraints progLocs progVars = (psi_conn, phi_lib)
    where
        allVarsWithLocs = zip (toIOsList progVars) (toIOsList progLocs)
        psi_conn = sAnd [(xLoc .== yLoc) .=> (x .== y) | (x, xLoc) ← allVarsWithLocs, (y, yLoc) ← allVarsWithLocs]
        phi_lib =
            sAnd . toList $
                programInstructions progVars <&> \(Instruction (IOs inputVars outputVar) comp) →
                    specFunc (compSpec comp) inputVars outputVar


{- | Special version of 'createProgramVarsWith' for constant components.
A constant component is a component having 'specArity' \(=0\). The original
paper slightly touches this topic in the last paragraph of section 7.
This function always uses existential quantification and only operates on
constant components. The 'Program' returned from this function contains
'undefined' values for 'programIOs' and non-constant 'programInstructions'.
The user is expected to call 'createProgramVarsWith' later and then use
'combineProgramVars' to merge two results.
-}
createConstantVars
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ NonEmpty (comp a)
    -- ^ Component library.
    → Symbolic (Program (SBV a) (comp a))
createConstantVars library = do
    componentVars ← forM library $ \comp → do
        if isConstantComponent comp
            then do
                compOutputVar ← free $ mkOutputVarName $ compName comp
                return $ Instruction (IOs [] compOutputVar) comp
            else return $ Instruction undefined comp

    return $ Program undefined componentVars


{- | Given a 'Program' of constant-only components and a 'Program' of non-constant
components, combine them into a single 'Program'.
-}
combineProgramVars
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ Program (SBV a) (comp a)
    -- ^ The result of 'createConstantVars'
    → Program (SBV a) (comp a)
    -- ^ The result of 'createProgramVarsWith'
    → Program (SBV a) (comp a)
combineProgramVars lhProgram rhProgram =
    Program (programIOs rhProgram) $
        NE.zipWith selectInstruction (programInstructions lhProgram) (programInstructions rhProgram)
    where
        selectInstruction lhInst rhInst =
            if specArity (compSpec $ instructionComponent lhInst) == 0
                then lhInst
                else rhInst


{- | Smart version of 'getValue' for 'Instruction'.
For each component it gets solutions for location variable, effectively turning
'Instruction SLocation (comp a)' into 'Instruction Location (comp a)'.
For constant components it additionaly fills 'comp a' part of the structure
with its returning value.
-}
instructionGetValue
    ∷ ∀ a comp spec m
     . (SymVal a, SynthSpec spec a, SynthComponent comp spec a)
    ⇒ Instruction SLocation (comp a)
    → Instruction (SBV a) (comp a)
    → Query (Instruction Location (comp a))
instructionGetValue instLocs instVars = do
    locVals ← traverse getValue (instructionIOs instLocs)
    comp ←
        let comp = instructionComponent instLocs
         in if isConstantComponent comp
                then do
                    constValue ← getValue $ _out $ instructionIOs instVars
                    return $ putConstValue comp constValue
                else return comp
    return $ Instruction locVals comp


-- | The 'zipWithM' function generalizes 'zipWith' to arbitrary applicative functors.
zipWithNEM ∷ (Applicative m) ⇒ (a → b → m c) → NonEmpty a → NonEmpty b → m (NonEmpty c)
{-# INLINE zipWithNEM #-}
-- Inline so that fusion with zipWith and sequenceA have a chance to fire
-- See Note [Fusion for zipN/zipWithN] in List.hs]
zipWithNEM f xs ys = sequenceA (NE.zipWith f xs ys)


genericLength' ∷ (Foldable f, Num i) ⇒ f a → i
genericLength' = genericLength . toList


instance (EqSymbolic a) ⇒ EqSymbolic (NonEmpty a) where
    (x :| []) .== (y :| []) = x .== y
    (x :| xs) .== (y :| ys) = x .== y .&& xs .== ys


instance (OrdSymbolic a) ⇒ OrdSymbolic (NonEmpty a) where
    (x :| xs) .< (y :| ys) =
        x .< y .|| case (xs, ys) of
            ([], []) → sFalse
            ([], _) → sTrue
            (_, []) → sFalse
            (a : as, b : bs) → (a :| as) .< (b :| bs)


instance (Mergeable a) ⇒ Mergeable (NonEmpty a) where
    symbolicMerge f t xs ys
        | lxs == lys = NE.zipWith (symbolicMerge f t) xs ys
        | otherwise =
            cannotMerge
                "lists"
                ("Branches produce different sizes: " ++ show lxs ++ " vs " ++ show lys ++ ". Must have the same length.")
                "Use the 'SList' type (and Data.SBV.List routines) to model fully symbolic lists."
        where
            (lxs, lys) = (length xs, length ys)
            cannotMerge typ why hint =
                error $
                    unlines
                        [ ""
                        , "*** Data.SBV.Mergeable: Cannot merge instances of " <> typ <> "."
                        , "*** While trying to do a symbolic if-then-else with incompatible branch results."
                        , "***"
                        , "*** " <> why
                        , "*** "
                        , "*** Hint: " <> hint
                        ]
