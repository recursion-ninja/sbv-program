module Data.SBV.Program.SimpleLibrary(
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

    -- * Logic components
    bXor,
    bEquiv
  )
where

import Data.SBV
import Data.SBV.Program.Types


inc :: (SymVal a, Ord a, Num a) => SimpleComponent a
inc = SimpleComponent "inc" $ SimpleSpec 1 $ \[i] o -> o .== (i+1)

dec :: (SymVal a, Ord a, Num a) => SimpleComponent a
dec = SimpleComponent "dec" $ SimpleSpec 1 $ \[i] o -> o .== (i-1)

add :: (SymVal a, Ord a, Num a) => SimpleComponent a
add = SimpleComponent "add" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 + i2)

sub :: (SymVal a, Ord a, Num a) => SimpleComponent a
sub = SimpleComponent "sub" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 - i2)

mul :: (SymVal a, Ord a, Num a) => SimpleComponent a
mul = SimpleComponent "mul" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 * i2)


and :: (SymVal a, Ord a, Num a, Bits a) => SimpleComponent a
and = SimpleComponent "and" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 .&. i2)

or :: (SymVal a, Ord a, Num a, Bits a) => SimpleComponent a
or = SimpleComponent "or" $ SimpleSpec 2 $ \[i1,i2] o -> o .== (i1 .|. i2)

not :: (SymVal a, Ord a, Num a, Bits a) => SimpleComponent a
not = SimpleComponent "not" $ SimpleSpec 1 $ \[i1] o -> o .== complement i1


bXor = SimpleComponent "bXor" $ SimpleSpec 2 $ \[i1,i2] o -> o .== i1 .<+> i2

-- | Logical equivalence implemented in "tabular" style
bEquiv = SimpleComponent "bEquiv" $ SimpleSpec 2 $ \[i1,i2] o -> sAnd [
    sNot i1 .&& sNot i2 .=> o,
    i1 .&& sNot i2 .=> sNot o,
    sNot i1 .&& i2 .=> sNot o,
    i1 .&& i2 .=> o
  ]
