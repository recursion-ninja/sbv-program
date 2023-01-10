--
-- | This module implements an algorithm described in the
-- "Component-based Synthesis Applied to Bitvector Programs" paper.
--
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2010/02/bv.pdf
--
-- Given a program specification along with a library of available components
-- it synthesizes an actual program using an off-the-shelf SMT-solver.
--
-- The specification is an arbitrary datatype that is an instance of the 'SynthSpec' class.
-- The library is a list of 'SynthComponent' instances.
--
-- There are three entry points to this module: 'standardExAllProcedure', 'refinedExAllProcedure' and 'exAllProcedure'.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}

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

  -- * Auxiliary functions that make up synthesis procedures #aux#

  createProgramLocs,
  constrainLocs,
  createProgramVarsWith,
  createVarsConstraints,
  )
where

import Control.Monad
import Control.Monad.IO.Class
import Data.Either
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Ord (comparing)
import Data.Traversable (for)
import Data.SBV hiding (STuple)
import Data.SBV.Control

import Data.SBV.Program.SimpleLibrary
import Data.SBV.Program.Types
import Data.SBV.Program.Utils

import Text.Pretty.Simple (pPrint)


-- | Represents a failed run in 'standardExAllProcedure'. Corresponds to
-- __program variable__ \(S\) in the paper.
data STuple a = STuple {
    s_ios :: IOs a,
    s_comps :: [IOs a]
  }
  deriving Show


-- | An implementation of __StandardExAllSolver__ presented in section 6.1 of the paper.
-- As stated in the paper, this implementation boils down to exhaustive enumeration
-- of possible solutions, and as such isn't effective. It can be used to better
-- understand how the synthesis procedure works and provides a lot of debugging
-- output. Do not use this procedure for solving real problems.
standardExAllProcedure :: forall a comp spec .
  (SymVal a, Show a, SynthSpec spec a, SynthComponent comp spec a) =>
    -- | Component library
       [comp a]
    -- | Specification of program being synthesized
    -> spec a
    -> IO (Either SynthesisError (Program Location (comp a)))
standardExAllProcedure library spec = do
  -- generate a seed for S
  mbRes <- sampleSpec spec
  case mbRes of
      Nothing -> return $ Left ErrorSeedingFailed
      Just i0 -> do
        putStrLn "Seeding done, result:"
        print i0
        go 1 [STuple (i0 :: IOs a) []]
  where
    n = genericLength library
    numInputs = specArity spec
    m = n + numInputs
    go step s = do
      putStrLn "============="
      putStrLn "Synthesizing with s = "
      pPrint s
      -- Finite synthesis part
      r <- runSMT $ do
        progLocs <- createProgramLocs library numInputs

        constrainLocs m numInputs progLocs

        -- Unlike 'exAllProcedure' we call 'createProgramVarsWith' here multiple times
        -- Since we aren't using forall quantifier, we have to create variables
        -- for each STuple item in s.
        manyProgVars <- forM s $ \(STuple {..}) -> do
          let numInputs = genericLength $ _ins s_ios
          progVars <- createProgramVarsWith sbvExists library numInputs

          -- pin input/output variables (members of I and O sets) to values from S
          constrain $ fmap literal s_ios .== programIOs progVars
          -- on the first run we don't have values for component locations (members of T set in the paper)
          unless (null s_comps) $
            constrain $ map (fmap literal) s_comps .== map instructionIOs (programInstructions progVars)

          return progVars

        forM_ manyProgVars $ \progVars -> do
          let (IOs inputVars outputVar) = programIOs progVars
              (psi_conn, phi_lib) = createVarsConstraints progLocs progVars
          constrain $ (phi_lib .&& psi_conn) .=> specFunc spec inputVars outputVar

        query $ do
          r <- checkSat
          case r of
            Sat -> do
              solution <- mapM getValue (programIOs progLocs)
              componentLocVals <- traverse (bimapM getValue pure) (programInstructions progLocs)
              return $ Right (Program solution componentLocVals)
            Unsat -> return $ Left ErrorUnsat
            Unk -> Left . ErrorUnknown . show <$> getUnknownReason
      -- Verification part
      -- At this stage the 'currL' program represents a solution that is known to
      -- work for all values from S. We now check if this solution works for all
      -- values possible.
      fmap join $ for r $ \currL -> runSMT $ do
        liftIO $ do
          putStrLn "Synthesis step done, current solution:"
          putStrLn $ writePseudocode currL

        progLocs <- createProgramLocs library numInputs

        -- In the verification part we pin location variables L
        constrain $ (literal <$> programIOs currL) .== programIOs progLocs
        constrain $ sAnd $ zipWith (\x y -> literal x .== y) (concatMap (toList .instructionIOs) (programInstructions currL)) (concatMap (toList .instructionIOs) (programInstructions progLocs))

        progVars <- createProgramVarsWith sbvExists library numInputs

        let Program (IOs inputVars outputVar) componentVars = progVars
            (psi_conn, phi_lib) = createVarsConstraints progLocs progVars

        constrain $ sNot $ (phi_lib .&& psi_conn) .=> specFunc spec inputVars outputVar

        query $ do
          r <- checkSat
          io $ putStrLn "Verification step done"
          case r of
            Unsat -> do
              io $ do
                putStrLn "============="
                putStrLn ("Solution found after " ++ show step ++ " iterations")
              return $ Right currL
            Sat -> do
              io $ putStrLn "Solution does not work for all inputs"
              inputVals <- mapM getValue inputVars
              outputVal <- getValue outputVar
              componentVals <- mapM (traverse getValue . instructionIOs) componentVars
              io $ go (step + 1) $ STuple (IOs inputVals outputVal) componentVals : s


-- | An implementation of __RefinedExAllSolver__ presented in section 6.2 of the paper.
-- This is an improved version of 'standardExAllProcedure'. It only keeps input
-- values \(|\vec I|\) in \(S\) and uses different synthesis constraints on __synthesis__
-- and __verification__ steps.
refinedExAllProcedure :: forall a comp spec .
  (SymVal a, SynthSpec spec a, SynthComponent comp spec a) =>
    -- | Component library
       [comp a]
    -- | Specification of program being synthesized
    -> spec a
    -> IO (Either SynthesisError (Program Location (comp a)))
refinedExAllProcedure library spec = do
  mbRes <- sampleSpec spec
  case mbRes of
    Nothing -> return $ Left ErrorSeedingFailed
    Just r -> go 1 ([_ins r] :: [[a]])
  where
    n = genericLength library
    numInputs = specArity spec
    m = n + numInputs
    go step s = do
      -- Finite synthesis part
      r <- runSMT $ do
        progLocs <- createProgramLocs library numInputs

        constrainLocs m numInputs progLocs

        -- Unlike 'exAllProcedure' here we call 'createProgramVarsWith' multiple times
        -- Since we aren't using forall quantifier, we have to create variables
        -- for each I vector in s.
        manyProgVars <- forM s $ \inputVars_s -> do
          let numInputs = genericLength inputVars_s
          progVars <- createProgramVarsWith sbvExists library numInputs

          -- pin input variables (members of I set) to values from S
          constrain $ fmap literal inputVars_s .== _ins (programIOs progVars)

          return progVars

        forM_ manyProgVars $ \progVars -> do
          let (IOs inputVars outputVar) = programIOs progVars
              (psi_conn, phi_lib) = createVarsConstraints progLocs progVars
          constrain $ (phi_lib .&& psi_conn) .&& specFunc spec inputVars outputVar

        query $ do
          r <- checkSat
          case r of
            Sat -> Right <$> bitraverse getValue pure progLocs
            _ -> return $ Left ErrorUnsat
      -- Verification part
      -- At this stage the 'currL' program represents a solution that is known to
      -- work for all values from S. We now check if this solution works for all
      -- values possible.
      fmap join $ for r $ \currL -> runSMT $ do
        progLocs <- createProgramLocs library numInputs

        -- In the verification part we pin location variables L
        constrain $ (literal <$> programIOs currL) .== programIOs progLocs
        constrain $ sAnd $ zipWith (\x y -> literal x .== y) (concatMap (toList .instructionIOs) (programInstructions currL)) (concatMap (toList .instructionIOs) (programInstructions progLocs))

        progVars <- createProgramVarsWith sbvExists library numInputs

        let (Program (IOs inputVars outputVar) componentVars) = progVars
            (psi_conn, phi_lib) = createVarsConstraints progLocs progVars

        constrain $ (phi_lib .&& psi_conn) .&& sNot (specFunc spec inputVars outputVar)

        query $ do
          r <- checkSat
          case r of
            Unsat -> return $ Right currL
            Sat -> do
              inputVals <- mapM getValue inputVars
              outputVal <- getValue outputVar
              componentVals <- mapM (traverse getValue . instructionIOs) componentVars
              io $ go (step + 1) $ inputVals : s

-- | This procedure is not part of the paper. It uses forall quantification directly
-- when creating variables from the \(T\) set. As consequence it requires an SMT-solver
-- than can handle foralls (for instance, Z3). This procedure is the easiest to
-- understand.
exAllProcedure :: forall a comp spec .
  (SymVal a, SynthSpec spec a, SynthComponent comp spec a) =>
    -- | Component library
       [comp a]
    -- | Specification of program being synthesized
    -> spec a
    -> IO (Either SynthesisError (Program Location (comp a)))
exAllProcedure library spec =
  -- run SBV with 'allowQuantifiedQueries' to silence warnings about entering
  -- 'query' mode in presence of universally quantified variables
  runSMTWith (defaultSMTCfg {allowQuantifiedQueries = True}) $ do
    let n = genericLength library
        numInputs = specArity spec
        m = n + numInputs

    progLocs <- createProgramLocs library numInputs

    constrainLocs m numInputs progLocs

    progVars <- createProgramVarsWith sbvForall library numInputs

    let (Program (IOs inputVars outputVar) _) = progVars
        (psi_conn, phi_lib) = createVarsConstraints progLocs progVars

    constrain $ (phi_lib .&& psi_conn) .=> specFunc spec inputVars outputVar

    query $ do
      r <- checkSat
      case r of
        Sat -> do
          inputLocVals <- mapM getValue (_ins $ programIOs progLocs)
          outputLocVal <- getValue (_out $ programIOs progLocs)
          componentLocVals <- traverse (bimapM getValue pure) (programInstructions progLocs)
          return $ Right $ Program (IOs inputLocVals outputLocVal) (sortOn (_out . instructionIOs) componentLocVals)
        Unsat -> return $ Left ErrorUnsat
        Unk -> do
          reason <- getUnknownReason
          return $ Left $ ErrorUnknown $ "Unknown: " ++ show reason


-- | First step of each synthesis procedure. Given a library of components and
-- a number of program's inputs, it creates existentially quantified
-- __location variables__ (members of set \(L\) in the paper) for each component
-- and for the program itself.
createProgramLocs :: forall a comp spec . (SymVal a, SynthSpec spec a, SynthComponent comp spec a) => [comp a] -> Word -> Symbolic (Program SLocation (comp a))
createProgramLocs library numInputs = do
  inputLocs <- mapM sbvExists $ genericTake numInputs ["InputLoc" ++ show i | i <- [1..]] :: Symbolic [SLocation]
  outputLoc <- sbvExists "OutputLoc" :: Symbolic SLocation

  componentsWithLocs <- forM library $ \component -> do
    let n' = specArity $ compSpec component
    compInputLocs <- mapM sbvExists $ genericTake n' [mkInputLocName (compName component) i | i <- [1..]]
    compOutputLoc <- sbvExists $ mkOutputLocName $ compName component
    return $ Instruction (IOs compInputLocs compOutputLoc) component :: Symbolic (Instruction SLocation (comp a))

  return $ Program (IOs inputLocs outputLoc) componentsWithLocs


-- | Second step of each synthesis procedure. It applies constraints on
-- __location variables__ from section 5 of the original paper. These constraints
-- include __well-formedness constraint__ \(ψ_{wfp}\), __acyclicity constraint__
-- \(ψ_{acyc}\) and __consistency constraint__ \(ψ_{cons}\). Constraints are not
-- returned from this function, but are applied immediately. Section 5 of the
-- paper also talks about __connectivity constraint__ \(ψ_{conn}\), which is
-- not created here.
constrainLocs :: (SynthSpec spec a, SynthComponent comp spec a) =>
  -- | The \(M\) constant from the paper, which equals to \(N + |\vec I|\), where
  -- __N__ is the size of the library.
     Word
  -- | Number of program inputs \(|\vec I|\).
  -> Word
  -> Program SLocation (comp a) -> Symbolic ()
constrainLocs m numInputs (Program {..}) = do
  -- program inputs are assigned locations from 0 to numInputs
  forM_ (zip [0..] (_ins programIOs)) $ \(i, inputLoc) -> do
    constrain $ inputLoc .== literal i
  -- program output location should not be greater than the number of instructions
  constrain $ _out programIOs .< fromIntegral m

  forM_ programInstructions $ \(Instruction (IOs compInputLocs compOutputLoc) comp) -> do
    forM_ compInputLocs $ \inputLoc -> do
      -- psi_wfp for component inputs
      constrain $ inputLoc .>= literal 0
      constrain $ inputLoc .<= literal (fromIntegral $ m-1)
      -- psi_acyc
      constrain $ inputLoc .< compOutputLoc

    -- psi_wfp for component outputs
    constrain $ compOutputLoc .>= literal (fromIntegral numInputs)
    constrain $ compOutputLoc .<= literal (fromIntegral $ m-1)

    -- extra constraints supplied by user
    forM_ (extraLocConstrs comp) $ \extraConstr ->
      constrain $ extraConstr compInputLocs compOutputLoc

  -- psi_cons
  constrain $ distinct $ map (_out . instructionIOs) programInstructions


-- | Third step of the synthesis process. It creates variables that represent
-- actual inputs/outputs values (members of the set \(T\) in the paper). This
-- function resembles 'createProgramLocs', but unlike it allows creating both existentially
-- and universally quantified variables. Standard and Refined procedures pass
-- 'sbvExists' to create existentially quantified variables, while 'exAllProcedure'
-- uses 'sbvForall'.
createProgramVarsWith :: forall a comp spec . (SymVal a, SynthSpec spec a, SynthComponent comp spec a) =>
  -- | Variable creation function. Either 'sbvExists' or 'sbvForall'.
     (String -> Symbolic (SBV a))
  -- | Component library.
  -> [comp a]
  -- | Number of program inputs \(|\vec I|\).
  -> Word
  -> Symbolic (Program (SBV a) (comp a))
createProgramVarsWith sbvMakeFunc library numInputs = do
  inputVars <- mapM sbvMakeFunc $ genericTake numInputs ["Input" ++ show i | i <- [1..]]
  outputVar <- sbvMakeFunc "Output"

  componentVars <- forM library $ \comp -> do
    let n' = specArity $ compSpec comp
    compInputVars <- mapM sbvMakeFunc $ genericTake n' [mkInputVarName (compName comp) i | i <- [1..]]
    compOutputVar <- sbvMakeFunc $ mkOutputVarName $ compName comp
    return $ Instruction (IOs compInputVars compOutputVar) comp

  return $ Program (IOs inputVars outputVar) componentVars


-- | Last building block of the synthesis process. This function creates
-- \(ψ_{conn}\) and \(φ_{lib}\) constraints and return them.
createVarsConstraints :: SynthComponent comp spec a => Program SLocation (comp a) -> Program (SBV a) (comp a) -> (SBool, SBool)
createVarsConstraints progLocs progVars = (psi_conn, phi_lib)
  where
    allVarsWithLocs = zip (toIOsList progVars) (toIOsList progLocs)
    psi_conn = sAnd [(xLoc .== yLoc) .=> (x .== y) | (x, xLoc) <- allVarsWithLocs, (y, yLoc) <- allVarsWithLocs]
    phi_lib = sAnd $ flip map (programInstructions progVars) $
        \(Instruction (IOs inputVars outputVar) comp) -> specFunc (compSpec comp) inputVars outputVar

