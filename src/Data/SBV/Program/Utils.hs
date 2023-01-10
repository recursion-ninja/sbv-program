{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.SBV.Program.Utils (
  sampleSpec,

  mkVarName,
  mkInputLocName,
  mkOutputLocName,
  mkInputVarName,
  mkOutputVarName,

  writePseudocode,
  )
where

import Data.List (intercalate)
import Data.SBV
import Data.SBV.Control
import Data.SBV.Program.Types


-- | Given a 'SynthSpec' tries to generate a set of input/output values that satisfy the specification.
-- Uses solver under the hood.
sampleSpec :: forall a comp spec . (SymVal a, SynthSpec spec a) => spec a -> IO (Maybe (IOs a))
sampleSpec spec = runSMT $ do
    -- use solver to create initial values for I
    ins <- mkExistVars @a $ fromIntegral $ specArity spec
    out <- sbvExists_
    constrain $ specFunc spec ins out
    query $ do
      r <- checkSat
      case r of
        Sat -> Just <$> (IOs <$> mapM getValue ins <*> getValue out)
        _ -> pure Nothing


-- | Creates sanitized variable name suitable for SBV.
mkVarName :: String -- ^ Base name, which can be an empty string, in which case \"UnnamedComponent\" value will be used.
          -> Bool -- ^ Setting 'isLocation' to 'True' will append \"Loc\" to the name.
          -> Bool -- ^ If 'isOutput' is 'False' the value of 'i' is also appended to the name.
          -> Word -- ^ Number of an input. Can be 'undefined' for an output.
          -> String
mkVarName compName isLocation isOutput i = name1 ++ name2 ++ if not isOutput then show i else ""
  where
    name1 = if null compName then "UnnamedComponent" else compName
    name2 = (if isOutput then "Output" else "Input") ++ if isLocation then "Loc" else ""

-- | Shortcut for the more general 'mkVarName' function.
mkInputLocName compName = mkVarName compName True False
-- | Shortcut for the more general 'mkVarName' function.
mkOutputLocName compName = mkVarName compName True True undefined
-- | Shortcut for the more general 'mkVarName' function.
mkInputVarName compName = mkVarName compName False False
-- | Shortcut for the more general 'mkVarName' function.
mkOutputVarName compName = mkVarName compName False True undefined


-- | Renders the solution in SSA style.
writePseudocode :: SynthComponent comp spec a => Program Location (comp a) -> String
writePseudocode prog = unlines (header : body ++ ret)
  where
    prog' = sortInstructions prog
    header = concat [
          "function(",
          intercalate ", " $ map writeArg (_ins $ programIOs prog'),
          "):"
        ]
    body = flip map (programInstructions prog') $ \(Instruction (IOs {..}) comp) -> concat [
        "\t%",
        show _out,
        " = ",
        compName comp,
        " ",
        intercalate ", " $ map writeArg _ins
        ]
    ret = ["\treturn " ++ writeArg (_out $ programIOs prog')]
    writeArg loc = '%' : show loc
