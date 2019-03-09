{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}

module BitLaser.Ops
  ( Arith()
  , runArith
  , execArith
  , solveArith
  , XorExtension(..)
  , Var()
  , NumBits
  , addClause
  , addBinFormula
  , important
  -- * Declaring variables
  , int
  , numBitsInVar
  -- * Integer operations
  , add
  , addNoCarry
  , addL
  , addNoCarryL
  , mult
  , multNoCarry
  , multL
  , multNoCarryL
  , pow2
  , xor
  -- * Extendings bits
  , extendVar1Bit
  , extendVarNBit
  -- * Comparing variables
  , allDistinct
  , allEqualTo
  , lesserV
  , greaterV
  , eqV
  , notEqV
  , eq
  , notEq
  )
where

import           BitLaser.BinaryFormula
import           BitLaser.SATRunner

import           Control.Monad
import           Control.Monad.Trans.State.Strict
import           Data.Bits               hiding ( xor )
import qualified Data.ByteString.Char8         as B
import           Data.Foldable
import qualified Data.IntSet                   as IS
import qualified Data.IntMap                   as IM
import           Data.Maybe
import           Data.Traversable
import           System.IO

data ArithState = ArithState
  { clauses :: [Clause]
  , nextVar :: !Int
  , namedVariables :: [(String, Var)]
  , xorExtensionAllowed :: !Bool
  , importantVariables :: !IS.IntSet }

newtype Arith a = Arith (State ArithState a)
  deriving ( Applicative, Monad, Functor )

type NumBits = Int

-- | Is XOR extension available or not? (Only cryptominisat5 supports this).
data XorExtension = XorExtension | NoXorExtension
  deriving ( Eq, Ord, Show, Read )

-- | Represents a variable.
data Var = Var !Int !Int
  deriving ( Eq, Ord, Show, Read )

-- | Tells how many bits are in a variable.
numBitsInVar :: Var -> Int
numBitsInVar (Var x y) = (y - x) + 1

-- | Declares an unsigned integer.
int :: NumBits -> String -> Arith Var
int num_bits name = Arith $ do
  st <- get
  let var = Var (nextVar st) (nextVar st + num_bits - 1)
  put $ st { nextVar        = nextVar st + num_bits
           , namedVariables = (name, var) : namedVariables st
           }
  return var

-- | Marks a variable as important.
--
-- Only important variables are reported in some solver functions.
important :: Var -> Arith ()
important (Var low high) = Arith $ do
  st <- get
  put $ st
    { importantVariables = IS.union (importantVariables st)
                                    (IS.fromList [low .. high])
    }

-- | Inserts a raw clause to the problem.
addClause :: Clause -> Arith ()
addClause clause = Arith $ modify $ \st -> st { clauses = clause : clauses st }

-- | Inserts a binary formula to the problem.
addBinFormula :: BinFormula -> Arith ()
addBinFormula formula = do
  st <- Arith get
  let new_clauses = subFormulas (nextVar st) formula
      new_largest = max (nextVar st) (largestVariable new_clauses) + 1
  Arith $ put $ st { nextVar = new_largest }
  for_ new_clauses addClause

-- | Computes a XOR between two variables and returns a result.
xor :: Var -> Var -> Arith Var
xor v1 v2 = do
  st <- Arith get
  if xorExtensionAllowed st
    then xorWithExtension v1 v2
    else xorNoExtension v1 v2

xorWithExtension :: Var -> Var -> Arith Var
xorWithExtension v1 v2 | numBitsInVar v1 /= numBitsInVar v2 =
  error "xorWithExtension: number of bits must be the same"
xorWithExtension v1@(Var low1 _high1) (Var low2 _high2) = do
  result@(Var low3 _high3) <- int (numBitsInVar v1) "xor_ext_result"
  for_ [0 .. (numBitsInVar v1) - 1] $ \idx -> do
    let idx_low1 = low1 + idx
        idx_low2 = low2 + idx
        idx_low3 = low3 + idx
    addClause $ xorclause [Yes idx_low1, Yes idx_low2, No idx_low3]
  return result

xorNoExtension :: Var -> Var -> Arith Var
xorNoExtension v1 v2 | numBitsInVar v1 /= numBitsInVar v2 =
  error "xorNoExtension: number of bits must be the same"
xorNoExtension v1@(Var low1 _high1) (Var low2 _high2) = do
  result@(Var low3 _high3) <- int (numBitsInVar v1) "xor_noext_result"
  for_ [0 .. (numBitsInVar v1 - 1)] $ \idx -> do
    let idx_low1 = term $ low1 + idx
        idx_low2 = term $ low2 + idx
        idx_low3 = term $ low3 + idx
    addBinFormula $ implies (andd (nott idx_low1) idx_low2) idx_low3
    addBinFormula $ implies (andd idx_low1 idx_low2) (nott idx_low3)
    addBinFormula
      $ implies (andd (nott idx_low1) (nott idx_low2)) (nott idx_low3)
    addBinFormula $ implies (andd idx_low1 (nott idx_low2)) idx_low3
  return result

-- | Turns an Arith DSL into clauses that can be SAT solved.
--
-- Also returns names for variables and important variables.
runArith :: Arith () -> XorExtension -> ([Clause], [(String, Var)], IS.IntSet)
runArith (Arith st) xorextension =
  let final_state = execState st (ArithState [] 1 [] xorextension' IS.empty)
  in  ( clauses final_state
      , namedVariables final_state
      , importantVariables final_state
      )
  where xorextension' = xorextension == XorExtension

-- | Same as `runArith` but only returns the clauses.
execArith :: Arith () -> XorExtension -> [Clause]
execArith arith xorextension =
  let (clauses, _, _) = runArith arith xorextension in clauses

-- | Runs and solves `Arith` model, prints results to standard output.
solveArith :: Arith () -> XorExtension -> Solver -> IO ()
solveArith arith xorextension solver = do
  let (clauses, named_variables, important_variables) =
        runArith arith xorextension
  solution <- satSolve solver clauses important_variables (B.hPutStrLn stdout)
  case solution of
    Just solved -> for_ named_variables $ \(name, Var low high) ->
      when (all id [ IS.member idx important_variables | idx <- [low .. high] ])
        $ do
            let
              v :: Integer
              v = foldl'
                (\accum idx ->
                  accum
                    .|. ((fromIntegral $ noyes $ fromMaybe (No 0) $ IM.lookup
                           idx
                           solved
                         )
                        `shiftL` (fromIntegral $ idx - low)
                        )
                )
                0
                [low .. high]
            putStrLn $ name <> (replicate (30 - length name) ' ') <> show v
    Nothing -> putStrLn "UNSATISFIABLE"

true :: Int -> Arith ()
true idx =
  Arith $ modify $ \st -> st { clauses = clause [Yes idx] : clauses st }

false :: Int -> Arith ()
false idx =
  Arith $ modify $ \st -> st { clauses = clause [No idx] : clauses st }

-- | Asserts that two variables have the same value.
eqV :: Var -> Var -> Arith ()
eqV v1 v2 = do
  st <- Arith get
  if xorExtensionAllowed st
    then eqVXorExtension v1 v2
    else eqVNoXorExtension v1 v2

eqVXorExtension :: Var -> Var -> Arith ()
eqVXorExtension v1 v2 | numBitsInVar v1 /= numBitsInVar v2 =
  error $ "eqV: bits don't match: " <> show (numBitsInVar v1, numBitsInVar v2)
eqVXorExtension v1@(Var low1 _) (Var low2 _) =
  for_ [0 .. (numBitsInVar v1 - 1)] $ \idx -> do
    let low1_idx = idx + low1
        low2_idx = idx + low2
    addClause $ xorclause [Yes low1_idx, No low2_idx]

eqVNoXorExtension :: Var -> Var -> Arith ()
eqVNoXorExtension v1 v2 | numBitsInVar v1 /= numBitsInVar v2 =
  error $ "eqV: bits don't match: " <> show (numBitsInVar v1, numBitsInVar v2)
eqVNoXorExtension v1@(Var low1 _) (Var low2 _) =
  for_ [0 .. (numBitsInVar v1 - 1)] $ \idx -> do
    let low1_idx = term $ idx + low1
        low2_idx = term $ idx + low2
    addBinFormula $ iff low1_idx low2_idx

-- | Asserts that two variables do not have the same value.
notEqV :: Var -> Var -> Arith ()
notEqV v1 v2 | numBitsInVar v1 /= numBitsInVar v2 =
  error "notEqV: bits don't match"
notEqV v1@(Var low1 _) (Var low2 _) = do
  are_same <- for [0 .. (numBitsInVar v1 - 1)] $ \n -> do
    let low1_idx = term $ n + low1
    let low2_idx = term $ n + low2
    Var same_idx _ <- int 1 "same"
    addBinFormula $ iff (iff low1_idx low2_idx) (term same_idx)
    return same_idx
  addClause $ clause [ No s | s <- are_same ]

-- | Asserts that left variable is bigger than right variable.
lesserV :: Var -> Var -> Arith ()
lesserV v1 v2 | numBitsInVar v1 /= numBitsInVar v2 =
  error "lesser: must have same number of bits."
lesserV v1 v2 = do
  addBinFormula $ le v1 v2
  notEqV v1 v2
 where
  le v1@(Var low1 high1) (Var low2 high2) | numBitsInVar v1 > 1 = andd
    (nott $ andd (term high1) (nott $ term high2))
    (orr (andd (term high2) (nott $ term high1))
         (le (Var low1 (high1 - 1)) (Var low2 (high2 - 1)))
    )
  le (Var _ _) (Var low2 _) = term low2

-- | Asserts that left variable is greater than right variable.
greaterV :: Var -> Var -> Arith ()
greaterV v1 v2 = lesserV v2 v1

-- | Asserts that variable equals a constant.
--
-- It is not checked if the variable has as many bits as the constant.
eq :: Var -> Integer -> Arith ()
eq (Var low high) int = for_ [low .. high]
  $ \idx -> if testBit int (idx - low) then true idx else false idx

-- | Asserts that variable does not equal a constant.
--
-- It is not checked if the variable has as many bits as the constant.
notEq :: Var -> Integer -> Arith ()
notEq (Var low high) int = addBinFormula $ go low
 where
  go n =
    let inner = if testBit int (n - low) then nott (term n) else term n
    in  if n == high then inner else orr inner (go (n + 1))

-- | Returns a new variable, that otherwise equals a variable but with one
-- additional zero bit.
extendVar1Bit :: Var -> Arith Var
extendVar1Bit v1@(Var low _) = do
  st             <- Arith get
  v@(Var low2 _) <- int (numBitsInVar v1 + 1) "extend"
  for_ [0 .. (numBitsInVar v1 - 1)] $ \idx -> do
    let low1_idx = idx + low
        low2_idx = idx + low2
    if xorExtensionAllowed st
      then addClause $ xorclause [Yes low1_idx, No low2_idx]
      else addBinFormula $ iff (term low1_idx) (term low2_idx)
  addClause $ clause [No $ low2 + numBitsInVar v1]
  return v

-- | Returns a new variable, that otherwise equals a variable but with N
-- additional zero bits.
extendVarNBit :: Var -> Int -> Arith Var
extendVarNBit v1@(Var low _) bits = do
  st             <- Arith get
  v@(Var low2 _) <- int (numBitsInVar v1 + bits) "extend"
  for_ [0 .. (numBitsInVar v1 - 1)] $ \idx -> do
    let low1_idx = idx + low
        low2_idx = idx + low2
    if xorExtensionAllowed st
      then addClause $ xorclause [Yes low1_idx, No low2_idx]
      else addBinFormula $ iff (term low1_idx) (term low2_idx)
  for_ [0 .. bits - 1]
    $ \bit -> addClause $ clause [No $ low2 + numBitsInVar v1 + bit]
  return v

runCombiningTree :: Monad m => [a] -> (a -> a -> m a) -> m a
runCombiningTree []     _        = error "runCombiningTree: empty list"
runCombiningTree [item] _        = return item
runCombiningTree lst    combiner = do
  let (left, right) =
        (take (length lst `div` 2) lst, drop (length lst `div` 2) lst)
  left_combined  <- runCombiningTree left combiner
  right_combined <- runCombiningTree right combiner
  combiner left_combined right_combined

-- | Multiplies a list of numbers, unsigned. Does not extend bits to make sure result
-- can fit.
--
-- This means the multiplication is done 2 to the power of number of bits in
-- the input variables.
multNoCarryL :: [Var] -> Arith Var
multNoCarryL []     = error "multNoCarryL: empty list of multiplications."
multNoCarryL [item] = return item
multNoCarryL lst    = runCombiningTree lst multNoCarry

-- | Multiplies a list of numbers, unsigned. This will extend the number of bits in the
-- result to guarantee the result can fit.
multL :: [Var] -> Arith Var
multL []     = error "multL: empty list of multiplications."
multL [item] = return item
multL lst    = runCombiningTree lst mult

-- | Sums a list of numbers, unsigned. This will extend the number of bits in
-- the result to guarantee the result can fit.
addL :: [Var] -> Arith Var
addL []     = error "addL: empty list of additions."
addL [item] = return item
addL lst    = runCombiningTree lst add

-- | Sums a list of numbers, unsigned. Does not extend bits in the result,
-- which means the result will wrap around modulo 2 to the power of number of
-- bits in an input variable.
addNoCarryL :: [Var] -> Arith Var
addNoCarryL []    = error "addNoCarryL: empty list of additions."
addNoCarryL items = addNoCarryL' items

addNoCarryL' :: [Var] -> Arith Var
addNoCarryL' []            = error "addNoCarryL: empty list of additions."
addNoCarryL' [item]        = return item
addNoCarryL' [x, y]        = addNoCarry x y
addNoCarryL' (x : y : lst) = do
  intermediate <- addNoCarry x y
  addNoCarryL' (intermediate : lst)

-- | Multiplies two unsigned variables and stores result to third variable.
--
-- Does not extend bits in result so this will be modulo 2 to the number of
-- bits in an input variable.
multNoCarry :: Var -> Var -> Arith Var
multNoCarry v1 v2 | numBitsInVar v1 /= numBitsInVar v2 = do
  error "multNoCarry: number of bits must be the same."
multNoCarry v1@(Var low1 _) (Var low2 _) = do
  intermediate_values <- for [0 .. numBitsInVar v1 - 1] $ \idx -> do
    intermediate2 <- int (numBitsInVar v1) "intermediate"
    addBinFormula $ implies (nott (term $ low1 + idx)) $ allZeroV intermediate2
    addBinFormula $ implies (term $ low1 + idx) $ goEqualsShift 0
                                                                idx
                                                                intermediate2
    return intermediate2
  addNoCarryL intermediate_values
 where
  goEqualsShift n shift inter@(Var ilow _) =
    let lowerbit = n - shift
        inner    = if lowerbit < 0 || lowerbit >= numBitsInVar v1
          then nott (term (ilow + n))
          else iff (term $ low2 + lowerbit) (term (ilow + n))
    in  if n + 1 < numBitsInVar inter
          then andd (goEqualsShift (n + 1) shift inter) inner
          else inner

-- | Multiplies two numbers, unsigned. Extends result bits so that it is
-- guaranteed the result can fit.
mult :: Var -> Var -> Arith Var
mult v1 v2 | numBitsInVar v1 < numBitsInVar v2 = do
  v1' <- extendVarNBit v1 (numBitsInVar v2 - numBitsInVar v1)
  mult v1' v2
mult v1 v2 | numBitsInVar v1 > numBitsInVar v2 = do
  v2' <- extendVarNBit v2 (numBitsInVar v1 - numBitsInVar v2)
  mult v1 v2'
mult v1@(Var low1 _) (Var low2 _) = do
  intermediate_values <- for [0 .. numBitsInVar v1 - 1] $ \idx -> do
    intermediate2 <- int (numBitsInVar v1 * 2) "intermediate"
    addBinFormula $ implies (nott (term $ low1 + idx)) $ allZeroV intermediate2
    addBinFormula $ implies (term $ low1 + idx) $ goEqualsShift 0
                                                                idx
                                                                intermediate2
    return intermediate2
  addNoCarryL intermediate_values
 where
  goEqualsShift n shift inter@(Var ilow _) =
    let lowerbit = n - shift
        inner    = if lowerbit < 0 || lowerbit >= numBitsInVar v1
          then nott (term (ilow + n))
          else iff (term $ low2 + lowerbit) (term (ilow + n))
    in  if n + 1 < numBitsInVar inter
          then andd (goEqualsShift (n + 1) shift inter) inner
          else inner

allZeroV :: Var -> BinFormula
allZeroV (Var low high) = allZero [low .. high]

allZero :: [Int] -> BinFormula
allZero []             = error "allZero: no bits"
allZero [x           ] = nott (term x)
allZero (x : y : rest) = andd (nott $ term x) (allZero (y : rest))

-- | Adds two numbers together, unsigned. The result is not extended with bits
-- so the result is modulo 2 to the power of number of bits in an input
-- variable.
addNoCarry :: Var -> Var -> Arith Var
addNoCarry v1 v2 = add' v1 v2 False

-- | Adds two numbers together, unsigned. The result is bit extended so that it is guaranteed
-- to fit in result.
add :: Var -> Var -> Arith Var
add v1 v2 = add' v1 v2 True

add' :: Var -> Var -> Bool -> Arith Var
add' v1 v2 use_carry | numBitsInVar v1 > numBitsInVar v2 = do
  v2' <- extendVarNBit v2 (numBitsInVar v1 - numBitsInVar v2)
  add' v1 v2' use_carry
add' v1 v2 use_carry | numBitsInVar v1 < numBitsInVar v2 = do
  v1' <- extendVarNBit v1 (numBitsInVar v2 - numBitsInVar v1)
  add' v1' v2 use_carry
add' v1 v2 use_carry = do
  st <- Arith get
  if xorExtensionAllowed st
    then addWithXorExtension v1 v2 use_carry
    else addWithNoXorExtension v1 v2 use_carry

addWithXorExtension :: Var -> Var -> Bool -> Arith Var
addWithXorExtension v1 v2 _ | numBitsInVar v1 /= numBitsInVar v2 =
  error $ "addwithNoXorExtension: number of bits must be the same, got " <> show
    (numBitsInVar v1, numBitsInVar v2)
addWithXorExtension v1@(Var low1 _) (Var low2 _) use_carry = do
  result <- int final_bits "add_xorext_result"
  go 0 result Nothing
  return result
 where
  final_bits = if use_carry then numBitsInVar v1 + 1 else numBitsInVar v1

  go n result@(Var low3 high3) previous_overload | n <= numBitsInVar v1 - 1 = do
    let idx_low1 = n + low1
        idx_low2 = n + low2
        idx_low3 = n + low3
        is_last  = n + 1 > numBitsInVar v1 - 1
    overload <- if
      | is_last && use_carry -> return $ Just $ Var high3 high3
      | use_carry            -> fmap Just $ int 1 $ "carry flag " <> show n
      | not is_last          -> fmap Just $ int 1 $ "carry flag " <> show n
      | otherwise            -> pure Nothing
    case previous_overload of
      Nothing -> do
        addClause $ xorclause [Yes idx_low1, Yes idx_low2, No idx_low3]
        case overload of
          Just (Var overload_low_idx _) -> do
            addClause $ clause [No idx_low1, No idx_low2, Yes overload_low_idx]
            addClause $ clause [Yes idx_low1, No overload_low_idx]
            addClause $ clause [Yes idx_low2, No overload_low_idx]
          _ -> return ()
      Just (Var previous_overload_low_idx _) -> do
        addClause $ xorclause
          [ Yes idx_low1
          , Yes idx_low2
          , Yes previous_overload_low_idx
          , No idx_low3
          ]
        case overload of
          Just (Var overload_low_idx _) -> do
            addClause $ clause
              [ No idx_low1
              , No idx_low2
              , No previous_overload_low_idx
              , Yes overload_low_idx
              ]
            addClause $ clause [No idx_low1, No idx_low2, Yes overload_low_idx]
            addClause
              $ clause
                  [ No idx_low1
                  , No previous_overload_low_idx
                  , Yes overload_low_idx
                  ]
            addClause
              $ clause
                  [ No idx_low2
                  , No previous_overload_low_idx
                  , Yes overload_low_idx
                  ]
            addClause
              $ clause
                  [ Yes idx_low1
                  , Yes previous_overload_low_idx
                  , No overload_low_idx
                  ]
            addClause $ clause [Yes idx_low1, Yes idx_low2, No overload_low_idx]
            addClause
              $ clause
                  [ Yes idx_low2
                  , Yes previous_overload_low_idx
                  , No overload_low_idx
                  ]
          Nothing -> return ()
    go (n + 1) result overload

  go _ _ _ = return ()

addWithNoXorExtension :: Var -> Var -> Bool -> Arith Var
addWithNoXorExtension v1 v2 _ | numBitsInVar v1 /= numBitsInVar v2 =
  error $ "addwithNoXorExtension: number of bits must be the same, got " <> show
    (numBitsInVar v1, numBitsInVar v2)
addWithNoXorExtension v1@(Var low1 _) (Var low2 _) use_carry = do
  result <- int final_bits "add_result"
  go 0 result Nothing
  return result
 where
  final_bits = if use_carry then numBitsInVar v1 + 1 else numBitsInVar v1

  go n result@(Var low3 high3) previous_overload | n < numBitsInVar v1 = do
    let is_last  = n == numBitsInVar v1 - 1
        idx_low1 = n + low1
        idx_low2 = n + low2
        idx_low3 = n + low3
    overload <- if
      | not is_last          -> Just <$> int 1 "carry flag"
      | is_last && use_carry -> return $ Just (Var high3 high3)
      | otherwise            -> return Nothing
    case previous_overload of
      Nothing -> do
        -- If both idx1_low1 and idx_low2 are zero, result must be zero
        addClause $ clause [Yes idx_low1, Yes idx_low2, No idx_low3]
        -- If both idx1_low1 and idx_low2 are positive, result must also be
        -- zero.
        addClause $ clause [No idx_low1, No idx_low2, No idx_low3]
        -- This leaves cases where just one of them is positive
        addClause $ clause [No idx_low1, Yes idx_low2, Yes idx_low3]
        addClause $ clause [No idx_low2, Yes idx_low1, Yes idx_low3]

        case overload of
          Just (Var overload_idx _) -> do
            -- Overload gets set if both idx1_low1 and idx_low2 are true
            -- And otherwise no.
            addClause $ clause [No idx_low1, No idx_low2, Yes overload_idx]
            addClause $ clause [Yes idx_low1, No overload_idx]
            addClause $ clause [Yes idx_low2, No overload_idx]
          _ -> return ()

      Just (Var previous_overload_idx _) -> do
        -- all cases where overload bit is 1
        addClause $ clause
          [No previous_overload_idx, No idx_low1, No idx_low2, Yes idx_low3]
        addClause $ clause
          [No previous_overload_idx, Yes idx_low1, No idx_low2, No idx_low3]
        addClause $ clause
          [No previous_overload_idx, No idx_low1, Yes idx_low2, No idx_low3]
        addClause $ clause
          [No previous_overload_idx, Yes idx_low1, Yes idx_low2, Yes idx_low3]
        addClause $ clause
          [Yes previous_overload_idx, No idx_low1, No idx_low2, No idx_low3]
        addClause $ clause
          [Yes previous_overload_idx, Yes idx_low1, No idx_low2, Yes idx_low3]
        addClause $ clause
          [Yes previous_overload_idx, No idx_low1, Yes idx_low2, Yes idx_low3]
        addClause $ clause
          [Yes previous_overload_idx, Yes idx_low1, Yes idx_low2, No idx_low3]
        case overload of
          Just (Var overload_idx _) -> do
            -- If two bits are set, then overload must be set
            addClause $ clause [No idx_low1, No idx_low2, Yes overload_idx]
            addClause $ clause
              [No previous_overload_idx, No idx_low1, Yes overload_idx]
            addClause $ clause
              [No previous_overload_idx, No idx_low2, Yes overload_idx]
            -- If two bits are unset, then overload must not be set
            addClause $ clause [Yes idx_low1, Yes idx_low2, No overload_idx]
            addClause $ clause
              [Yes previous_overload_idx, Yes idx_low2, No overload_idx]
            addClause $ clause
              [Yes previous_overload_idx, Yes idx_low1, No overload_idx]
          Nothing -> return ()
    go (n + 1) result overload

  go _ _ _ = return ()

-- | Raises variable to power of two and returns it.
pow2 :: Var -> Arith Var
pow2 var = mult var var

-- | Asserts that all listed variables are different from each other.
allDistinct :: [Var] -> Arith ()
allDistinct []         = return ()
allDistinct [_       ] = return ()
allDistinct (a : rest) = do
  for_ rest $ \b -> notEqV a b
  allDistinct rest

-- | Asserts all listed variables are equal to the variable on the right.
allEqualTo :: [Var] -> Var -> Arith ()
allEqualTo []  _   = return ()
allEqualTo lst tgt = for_ lst $ \b -> eqV b tgt
