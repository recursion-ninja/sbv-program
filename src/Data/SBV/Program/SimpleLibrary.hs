module Data.SBV.Program.SimpleLibrary(
    Data.SBV.Program.SimpleLibrary.const,
    concrete,

    -- * Arithmetic components
    inc,
    dec,
    add,
    sub,
    mul,

    -- * Bitwise logic components
    Data.SBV.Program.SimpleLibrary.and,
    Data.SBV.Program.SimpleLibrary.or,
    Data.SBV.Program.SimpleLibrary.not,
    Data.SBV.Program.SimpleLibrary.shl,
    Data.SBV.Program.SimpleLibrary.shr,

    -- * Logic components
    bXor,
    bNand,
    bEquiv
  )
where

import Data.SBV
import Data.SBV.Program.Types


const = mkSimpleComp "const" $ SimpleSpec 0 $ \[] o -> sTrue
concrete val = mkSimpleComp "const" $ SimpleSpec 0 $ \[] o -> o .== literal val


inc :: (SymVal a, Ord a, Num a) => SimpleComponent a
inc = mkSimpleComp "inc" $ SimpleSpec 1 $ \[i] o -> o .== (i+1)

dec :: (SymVal a, Ord a, Num a) => SimpleComponent a
dec = mkSimpleComp "dec" $ SimpleSpec 1 $ \[i] o -> o .== (i-1)

add :: (SymVal a, Ord a, Num a) => SimpleComponent a
add = mkSimpleComp "add" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 + i2)

sub :: (SymVal a, Ord a, Num a) => SimpleComponent a
sub = mkSimpleComp "sub" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 - i2)

mul :: (SymVal a, Ord a, Num a) => SimpleComponent a
mul = mkSimpleComp "mul" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 * i2)


and :: (SymVal a, Ord a, Num a, Bits a) => SimpleComponent a
and = mkSimpleComp "and" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 .&. i2)

or :: (SymVal a, Ord a, Num a, Bits a) => SimpleComponent a
or = mkSimpleComp "or" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 .|. i2)

not :: (SymVal a, Ord a, Num a, Bits a) => SimpleComponent a
not = mkSimpleComp "not" $ SimpleSpec 1 $ \[i1] o -> o .== complement i1

shl :: (SymVal a, Ord a, Num a, Bits a, SIntegral a) => SimpleComponent a
shl = mkSimpleComp "shl" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 `sShiftLeft` i2)

shr :: (SymVal a, Ord a, Num a, Bits a, SIntegral a) => SimpleComponent a
shr = mkSimpleComp "shr" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 `sShiftRight` i2)

bXor :: SimpleComponent Bool
bXor = mkSimpleComp "bXor" $ SimpleSpec 2 $ \[i1,i2] o -> o .== i1 .<+> i2

bNand :: SimpleComponent Bool
bNand = mkSimpleComp "bNand" $ SimpleSpec 2 $ \[i1,i2] o -> o .== sNot (i1 .&& i2)

-- | Logical equivalence implemented in "tabular" style
bEquiv :: SimpleComponent Bool
bEquiv = mkSimpleComp "bEquiv" $ SimpleSpec 2 $ \[i1,i2] o -> sAnd [
    sNot i1 .&& sNot i2 .=> o,
    i1 .&& sNot i2 .=> sNot o,
    sNot i1 .&& i2 .=> sNot o,
    i1 .&& i2 .=> o
  ]
