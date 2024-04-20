{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.SBV.Program.Utils (
    sampleSpec,
    isConstantComponent,
    mkVarName,
    mkInputLocName,
    mkOutputLocName,
    mkInputVarName,
    mkOutputVarName,
    writePseudocode,
) where

import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.List (intercalate)
import Data.List.NonEmpty qualified as NE
import Data.SBV
import Data.SBV.Control
import Data.SBV.Program.Types (
    IOs (..),
    Instruction (..),
    Location (..),
    Program (..),
    SynthComponent (..),
    SynthSpec (specArity, specFunc),
    sortInstructions,
 )
import Numeric.Natural


{- | Given a 'SynthSpec' tries to generate a set of input/output values that satisfy the specification.
Uses solver under the hood.
-}
sampleSpec
    ∷ ∀ a comp spec
     . (SymVal a, SynthSpec spec a)
    ⇒ spec a
    → IO (Maybe (IOs a))
sampleSpec spec =
    runSMT $
        let arity ∷ Natural
            arity = fromIntegral $ specArity spec

            --        opt :: ExistsN n "Inputs" a -> Exists "Output" a -> SBool
            --        opt (ExistsN ins) (Exists out) = specFunc spec ins out

            execution ∷ Symbolic (Maybe (IOs a))
            execution = do
                ins ← mkFreeVars @a . fromIntegral $ specArity spec
                out ← free "Output"

                let beseechment ∷ Query (Maybe (IOs a))
                    beseechment = do
                        r ← checkSat
                        case r of
                            Sat → Just <$> (IOs <$> mapM getValue ins <*> getValue out)
                            _ → pure Nothing

                --            ofArity :: SNat n -> ExistsN n "Input"
                --            ofArity = \

                --            withSomeSNat arity ofArity

                -- use solver to create initial values for I
                -- (ins :: _) <- mkExistVars @a $ (fromIntegral $ specArity spec :: _)
                --    (ins :: _) <- pure $ Exists <$> (fromIntegral $ specArity spec :: _)
                --    (out :: _) <- sbvExists_ -- SymVal a => Symbolic (SBV a)
                --    ins <- mkExistVars @a $ fromIntegral $ specArity spec
                --            ExistsN ins <- pure
                --            out <- pure $ Exists $ sym "out" -- SymVal a => Symbolic (SBV a)
                -- sbvExists_ :: SymbolicT IO (SBV a)

                constrain $ specFunc spec ins out
                query beseechment
        in  execution


{- | Returns 'True' if the component is a __constant__ one. Constant components
have zero inputs (their 'specArity' \(=0\) ).
-}
isConstantComponent
    ∷ ∀ a comp spec
     . (SynthSpec spec a, SynthComponent comp spec a)
    ⇒ comp a
    → Bool
isConstantComponent comp = specArity (compSpec comp) == 0


-- | Creates sanitized variable name suitable for SBV.
mkVarName
    ∷ String
    -- ^ Base name, which can be an empty string, in which case \"UnnamedComponent\" value will be used.
    → Bool
    -- ^ Setting 'isLocation' to 'True' will append \"Loc\" to the name.
    → Bool
    -- ^ If 'isOutput' is 'False' the value of 'i' is also appended to the name.
    → Word
    -- ^ Number of an input. Can be 'undefined' for an output.
    → String
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
writePseudocode ∷ (Show a, SynthComponent comp spec a) ⇒ Program Location (comp a) → String
writePseudocode prog = unlines (header : toList body <> ret)
    where
        prog' = sortInstructions prog
        header =
            concat
                [ "function("
                , intercalate ", " $ map writeArg (_ins $ programIOs prog')
                , "):"
                ]
        body =
            programInstructions prog' <&> \(Instruction (IOs{..}) comp) →
                concat
                    [ "\t%"
                    , show _out
                    , " = "
                    , compName comp
                    , " "
                    , intercalate ", " $ map writeArg _ins
                    , if isConstantComponent comp then show $ getConstValue comp else ""
                    ]
        ret = ["\treturn " ++ writeArg (_out $ programIOs prog')]
        writeArg loc = '%' : show loc
