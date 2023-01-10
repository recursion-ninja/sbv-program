# Component-based synthesis of loop-free programs

This package implements a library for synthesizing programs as described in the
[Component-based Synthesis Applied to Bitvector Programs](https://www.microsoft.com/en-us/research/wp-content/uploads/2010/02/bv.pdf) paper.
It uses an off-the-shelf SMT solver via [sbv](https://hackage.haskell.org/package/sbv) library.

See [Examples.hs](https://github.com/arrowd/sbv-program/blob/master/src/Data/SBV/Program/Examples.hs) file to quickly get at using this.
For deeper understanding of library's internals see the Haddock documentation.

The code is structured and commented in such way that it follows variable naming
of the original paper.
