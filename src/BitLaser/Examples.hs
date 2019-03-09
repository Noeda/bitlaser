module BitLaser.Examples
  ( magicSquare33
  )
where

import           BitLaser.Ops

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
