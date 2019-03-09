{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module BitLaser.SATRunner
  ( Term(..)
  , terms
  , Solver(..)
  , Clause(..)
  , clause
  , xorclause
  , largestVariable
  , satSolve
  , noyes
  )
where

import           Control.Applicative
import           Control.Concurrent      hiding ( yield )
import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.State.Strict
import           Data.Attoparsec.ByteString.Char8
import qualified Data.ByteString               as B
import qualified Data.ByteString.Builder       as BB
import           Data.Foldable
import qualified Data.Vector                   as V
import qualified Data.IntSet                   as IS
import qualified Data.IntMap.Strict            as IM
import           Pipes
import qualified Pipes.ByteString              as P
import           System.IO
import           System.Process

data Term = Yes !Int | No !Int
  deriving ( Eq, Ord, Show, Read )

data Clause = Clause (V.Vector Term) | XorClause (V.Vector Term)
  deriving ( Eq, Ord, Show, Read )

noyes :: Term -> Int
noyes (Yes{}) = 1
noyes (No{} ) = 0

type Solution = IM.IntMap Term

{-# INLINE terms #-}
terms :: Traversal' Clause Term
terms action (Clause    terms) = Clause <$> traverse action terms
terms action (XorClause terms) = XorClause <$> traverse action terms

{-# INLINE clause #-}
clause :: Foldable f => f Term -> Clause
clause terms = Clause $ V.fromList $ toList terms

{-# INLINE xorclause #-}
xorclause :: Foldable f => f Term -> Clause
xorclause terms = XorClause $ V.fromList $ toList terms

largestVariable :: Foldable f => f Clause -> Int
largestVariable = foldl' folder 0
 where
  folder accum (Clause    terms) = foldl' folder2 accum terms
  folder accum (XorClause terms) = foldl' folder2 accum terms
  folder2 accum (Yes var) = max accum var
  folder2 accum (No  var) = max accum var

data Solver
  = Cryptominisat5
  | Lingeling
  | PLingeling
  | Treengeling
  | Maplesat
  deriving ( Eq, Ord, Show, Read )

solverProc :: Solver -> Int -> CreateProcess
solverProc Cryptominisat5 caps = proc
  "cryptominisat5"
  ["-t", show caps, "--verb", "2", "--xorcache", "1", "--maxxormat", "1200"]
solverProc Lingeling   _ = proc "lingeling" []
solverProc PLingeling  _ = proc "plingeling" []
solverProc Treengeling _ = proc "treengeling" []
solverProc Maplesat    _ = proc "maplesat" []

-- | Given a clause, turns it into a line of DIMACS file.
clauseToDIMACS :: Clause -> BB.Builder
clauseToDIMACS (Clause vec) = foldl' folder mempty vec <> "0\n"
 where
  folder builder term = case term of
    Yes v -> builder <> BB.intDec v <> " "
    No  v -> builder <> BB.intDec (negate v) <> " "
clauseToDIMACS (XorClause vec) = "x" <> clauseToDIMACS (Clause vec)

type ImportantVariables = IS.IntSet

data ConsumeOutputResult = UNSAT | SAT Solution | UnexpectedEnd | UnparseableText B.ByteString

{-# INLINE intercalateMonoid #-}
intercalateMonoid :: Monoid a => a -> [a] -> a
intercalateMonoid _    []         = mempty
intercalateMonoid _    [x       ] = x
intercalateMonoid item (x : rest) = x <> item <> intercalateMonoid item rest

consumeOutput :: Handle -> (B.ByteString -> IO ()) -> IO ConsumeOutputResult
consumeOutput pstdout solver_output = do
  result <-
    flip runStateT mempty
    $   runEffect
    $   (P.fromHandle pstdout *> pure (SAT mempty))
    >-> liner
    >-> line_reader
  return $ case result of
    (SAT{}, st) -> SAT st
    (ret  , _ ) -> ret
 where
  liner = go mempty
   where
    go line_accum = do
      line <- await
      let newline = line_accum <> line
      yieldlines newline

    yieldlines newline = case B.break (== 0xa) newline of
      (_bs, right_bs) | B.null right_bs -> go newline
      (bs, right_bs)                    -> do
        yield bs
        yieldlines (B.tail right_bs)

  line_reader = do
    line <- await
    if
      | "s UNSATISFIABLE" `B.isInfixOf` line -> return UNSAT
      | "s SATISFIABLE" `B.isInfixOf` line -> read_solution
      | otherwise -> do
        liftIO $ solver_output line
        line_reader

  read_solution = do
    line <- await
    if B.length line > 0 && "v " `B.isPrefixOf` line
      then do
        case parseOnly parse_terms (B.drop 2 line) of
          Left{}      -> return $ UnparseableText line
          Right terms -> do
            lift $ modify $ IM.union (IM.delete 0 terms)
            read_solution
      else read_solution

  parse_terms = go IM.empty
   where
    go immap = do
      term_val <- signed decimal
      void $ many (char ' ')
      let term_a    = abs term_val
          new_terms = IM.insert
            term_a
            (if term_val < 0 then No term_a else Yes term_a)
            immap
      (endOfInput *> pure new_terms) <|> go new_terms

satSolve
  :: (Foldable f, MonadIO m)
  => Solver
  -> f Clause
  -> ImportantVariables
  -> (B.ByteString -> IO ())
  -> m (Maybe Solution)
satSolve solver clauses important_variables solver_output =
  liftIO $ mask $ \restore -> do
    caps <- getNumCapabilities
    (Just pstdin, Just pstdout, _, phandle) <- createProcess
      (solverProc solver caps) { std_in  = CreatePipe
                               , std_out = CreatePipe
                               , std_err = Inherit
                               }

    let cleanup = do
          terminateProcess phandle
          hClose pstdin
          hClose pstdout

    flip finally cleanup $ restore $ do
      BB.hPutBuilder pstdin
        $  "c ind "
        <> intercalateMonoid " "
                             (fmap BB.intDec $ IS.toList important_variables)
        <> " 0\n"
      BB.hPutBuilder pstdin
        $  "p cnf "
        <> BB.intDec largest_var
        <> " "
        <> BB.intDec nclauses
        <> "\n"
      for_ clauses $ \clause -> do
        BB.hPutBuilder pstdin $ clauseToDIMACS clause
      hFlush pstdin
      hClose pstdin

      result <- consumeOutput pstdout solver_output
      case result of
        UnexpectedEnd ->
          error "SAT solver ended unexpectedly without a result."
        UnparseableText unparsed ->
          error $ "SAT solver gave us unparseable output: " <> show unparsed
        SAT solution -> return $ Just solution
        UNSAT        -> return Nothing
 where
  nclauses    = length $ toList clauses
  largest_var = largestVariable clauses
