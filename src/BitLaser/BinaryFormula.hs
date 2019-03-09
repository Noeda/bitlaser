module BitLaser.BinaryFormula
  ( BinFormula()
  , subFormulas
  , iff
  , nott
  , andd
  , orr
  , term
  , implies
  , anddL
  , orrL
  )
where

import           BitLaser.SATRunner

import           Control.Monad.Trans.State.Strict
import qualified Data.Vector                   as V

data BinFormula
  = And BinFormula BinFormula
  | Or BinFormula BinFormula
  | Not BinFormula
  | Implies BinFormula BinFormula
  | IFF BinFormula BinFormula
  | Term !Int
  deriving ( Eq, Ord, Show, Read )

implies :: BinFormula -> BinFormula -> BinFormula
implies b1 b2 = Or (Not b1) b2

andd :: BinFormula -> BinFormula -> BinFormula
andd = And

orr :: BinFormula -> BinFormula -> BinFormula
orr = Or

nott :: BinFormula -> BinFormula
nott = Not

term :: Int -> BinFormula
term = Term

iff :: BinFormula -> BinFormula -> BinFormula
iff f1 f2 = And (Implies f1 f2) (Implies f2 f1)

simpleFormulaToClauses :: BinFormula -> [Clause]
simpleFormulaToClauses (Term x            ) = [Clause (V.singleton (Yes x))]
simpleFormulaToClauses (Not  (Term x)     ) = [Clause (V.singleton (No x))]
simpleFormulaToClauses (IFF (Term x) right) = case right of
  Term y -> [clause [No x, Yes y], clause [Yes x, No y]]
  And (Term y) (Term z) ->
    [clause [No x, Yes y], clause [No x, Yes z], clause [No y, No z, Yes x]]
  Or (Term y) (Term z) ->
    [clause [No x, Yes y, Yes z], clause [Yes x, No y], clause [Yes x, No z]]
  Not (Term y) -> [clause [No x, No y], clause [Yes x, Yes y]]
  -- This seems to not work.
  -- This is why `implies` function uses Or instead of Implies
  Implies (Term y) (Term z) ->
    [clause [No x, No y, Yes z], clause [Yes x, Yes y], clause [Yes x, No z]]
  _ -> error "impossible"

simpleFormulaToClauses formula =
  error $ "not a simple formula: " <> show formula

-- | Turns a binary formula into CNF clauses.
--
-- Supply lowest variable index to be used. The returned clauses will have
-- variables either as low as 'base' or higher.
subFormulas :: Int -> BinFormula -> [Clause]
subFormulas base formula =
  mconcat $ fmap simpleFormulaToClauses $ snd $ flip execState (base, []) $ do
    final <- go formula
    emit final
 where
  emit term = modify $ \(base, lst) -> (base, term : lst)
  nextIdx = do
    (base, lst) <- get
    put $ (base + 1, lst)
    return base
  go (Term x       ) = return (Term x)
  go (Not  (Term x)) = do
    v <- nextIdx
    emit (IFF (Term v) (Not (Term x)))
    return (Term v)
  go (And bformula1 bformula2) = do
    left  <- go bformula1
    right <- go bformula2
    v     <- nextIdx
    emit (IFF (Term v) (And left right))
    return (Term v)
  go (Or bformula1 bformula2) = do
    left  <- go bformula1
    right <- go bformula2
    v     <- nextIdx
    emit (IFF (Term v) (Or left right))
    return (Term v)
  go (Not bformula) = do
    left <- go bformula
    v    <- nextIdx
    emit (IFF (Term v) (Not left))
    return (Term v)
  go (Implies bformula1 bformula2) = do
    left  <- go bformula1
    right <- go bformula2
    v     <- nextIdx
    emit (IFF (Term v) (Implies left right))
    return (Term v)
  go (IFF bformula1 bformula2) = do
    left  <- go bformula1
    right <- go bformula2
    v     <- nextIdx
    emit (IFF (Term v) (IFF left right))
    return (Term v)

-- | Utility function that will combine lots of binary formulas with AND.
anddL :: [BinFormula] -> BinFormula
anddL []             = orr (term 1) (nott (term 1))
anddL [x]            = x
anddL [x, y]         = andd x y
anddL (x : y : rest) = andd x (anddL (y : rest))

-- | Utility function that will combine lots of binary formulas with OR.
orrL :: [BinFormula] -> BinFormula
orrL []             = orr (term 1) (nott (term 1))
orrL [x]            = x
orrL [x, y]         = orr x y
orrL (x : y : rest) = orr x (orrL (y : rest))
