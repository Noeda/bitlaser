Bitlaser
--------

This is a bit-blaster DSL for Haskell that turns a program with integer
operations into SAT problems to be solved with SAT solvers.

It is similar to Boolector and z3 for integer problems. But in Haskell.

I'm using this for bunch of my personal projects where I'm trying to solve
various problems. I would not consider this a complete project I would
recommend for generel use.

It expects a SAT solver on command line. You pass the desired SAT solver to
`solveArith` function (see example below). Any SAT solver that supports DIMACS
should work but you will need to add it to `Solvers` type.

Here's an example to solve a magic square, with 12-bit unsigned integers.

```haskell
import BitLaser.Ops
import BitLaser.SATRunner

magicSquare33 :: Arith ()
magicSquare33 = do
  a <- int 12 "a"
  b <- int 12 "b"
  c <- int 12 "c"
  d <- int 12 "d"
  e <- int 12 "e"
  f <- int 12 "f"
  g <- int 12 "g"
  h <- int 12 "h"
  i <- int 12 "i"

  important a
  important b
  important c
  important d
  important e
  important f
  important g
  important h
  important i

  sum1      <- addL [a, b, c]
  sum2      <- addL [d, e, f]
  sum3      <- addL [g, h, i]

  sum4      <- addL [a, d, g]
  sum5      <- addL [b, e, h]
  sum6      <- addL [c, f, i]

  sum7      <- addL [a, e, i]
  sum8      <- addL [g, e, c]

  total_sum <- int (numBitsInVar sum1) "total_sum"

  allDistinct [a, b, c, d, e, f, g, h, i]
  allEqualTo [sum1, sum2, sum3, sum4, sum5, sum6, sum7, sum8] total_sum

main :: IO ()
main = solveArith magicSquare33 XorExtension Cryptominisat5
```
