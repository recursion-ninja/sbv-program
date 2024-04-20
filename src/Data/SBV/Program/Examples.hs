--

{- | These examples can from GHCi by importing this module.
To get a human-readable pseudocode for the solution use

@
ghci> Right res <- someExample
ghci> putStrLn $ writePseudocode res
@
-}
module Data.SBV.Program.Examples (
    -- * Reset most significant set bit
    paperRunningExampleSpec,
    paperRunningExample,

    -- * Quadratic equation
    quadEquExampleSpec,
    quadEquExample,

    -- * Transform boolean formula into NAND-only expression
    nandifyExample,
) where

import Data.List
import Data.List.NonEmpty (NonEmpty (..))
import Data.SBV
import Data.SBV.Program
import Data.SBV.Program.SimpleLibrary as Lib


{- | A running example from the original paper. The function should reset the
least significant set bit of a 8-byte word:
>>> 0001 0010 -> 0000 0010
-}
paperRunningExampleSpec ∷ SimpleSpec Word8
paperRunningExampleSpec = SimpleSpec 1 $ \[i] o → sAnd $ flip map [7, 6 .. 0] $ \t →
    (sTestBit i t .&& sAnd (flip map [t - 1, t - 2 .. 0] $ \j → sNot $ sTestBit i j))
        .=> (sNot (sTestBit o t) .&& sAnd (flip map (t `delete` [7, 6 .. 0]) $ \j → sTestBit i j .== sTestBit o j))


paperRunningExample = refinedExAllProcedure (Lib.and :| [Lib.dec]) paperRunningExampleSpec


-- | Synthesizes a formula for the quadratic equation \(x^2 - 2x + 1 = 0\)
quadEquExampleSpec ∷ SimpleSpec Int32
quadEquExampleSpec = SimpleSpec 1 $ \[i] o →
    sAnd
        [ i .== 1 .=> o .== 0
        , i .== 4 .=> o .== 9
        ]


quadEquExample = refinedExAllProcedure (Lib.mul :| [Lib.add, Lib.sub, Lib.inc]) quadEquExampleSpec


{- | Reimplement arbitrary boolean formula with only NAND components.
Example usage:

@
nandifyExample 2 (SimpleSpec 2 $ \[i1, i2] o -> o .== (i1 .&& i2))
@
-}
nandifyExample
    ∷ Int
    -- ^ Amount of NAND components available
    → SimpleSpec Bool
    -- ^ Specification of the desired function
    → IO (Either SynthesisError (Program Location (SimpleComponent Bool)))
nandifyExample size = refinedExAllProcedure library
    where
        library = Lib.const :| [Lib.const] <> replicate size Lib.bNand
