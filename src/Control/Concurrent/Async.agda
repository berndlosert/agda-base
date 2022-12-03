module Control.Concurrent.Async where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Concurrent
open import Data.List as List using ()
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    f t : Set -> Set

-------------------------------------------------------------------------------
-- Async
-------------------------------------------------------------------------------

postulate
  Async : Set -> Set
  async : IO a -> IO (Async a)
  wait : Async a -> IO a
  waitAny : List (Async a) -> IO (Pair (Async a) a)
  waitEither : Async a -> Async b -> IO (Either a b)
  waitEither* : Async a -> Async b -> IO Unit
  waitBoth : Async a -> Async b -> IO (Pair a b)
  waitBoth* : Async a -> Async b -> IO Unit
  cancel : Async a -> IO Unit
  withAsync : IO a -> (Async a -> IO b) -> IO b

race : IO a -> IO b -> IO (Either a b)
race l r =
  withAsync l \ a ->
  withAsync r \ b ->
  waitEither a b

race* : IO a -> IO b -> IO Unit
race* l r =
  withAsync l \ a ->
  withAsync r \ b ->
  waitEither* a b

concurrently : IO a -> IO b -> IO (Pair a b)
concurrently l r =
  withAsync l \ a ->
  withAsync r \ b ->
  waitBoth a b

concurrently* : IO a -> IO b -> IO Unit
concurrently* l r = ignore (concurrently l r)

-------------------------------------------------------------------------------
-- Async FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC

  import Control.Concurrent
  import Control.Concurrent.STM.TMVar
  import Control.Exception
  import Control.Monad
  import Control.Monad.STM

  data Async a = Async {
      asyncThread :: !ThreadId,
      _asyncWait :: STM (Either SomeException a)
    }

  asyncUsing :: (IO () -> IO ThreadId) -> IO a -> IO (Async a)
  asyncUsing doFork = \ action -> do
    var <- newEmptyTMVarIO
    t <- mask $ \ restore ->
      doFork (try (restore action) >>= atomically . putTMVar var)
    pure (Async t (readTMVar var))

  async :: IO a -> IO (Async a)
  async = asyncUsing forkIO

  waitCatchSTM :: Async a -> STM (Either SomeException a)
  waitCatchSTM (Async _ w) = w

  waitCatch :: Async a -> IO (Either SomeException a)
  waitCatch = tryAgain . atomically . waitCatchSTM
    where tryAgain f = f `catch` (\ BlockedIndefinitelyOnSTM -> f)

  waitSTM :: Async a -> STM a
  waitSTM a = do
     r <- waitCatchSTM a
     either throwSTM pure r

  wait :: Async a -> IO a
  wait = tryAgain . atomically . waitSTM
    where tryAgain f = f `catch` (\ BlockedIndefinitelyOnSTM -> f)

  waitAnySTM :: [Async a] -> STM (Async a, a)
  waitAnySTM asyncs =
      foldr orElse retry
        (map (\ a -> do r <- waitSTM a; pure (a, r)) asyncs)

  waitAny :: [Async a] -> IO (Async a, a)
  waitAny = atomically . waitAnySTM

  waitEitherSTM :: Async a -> Async b -> STM (Either a b)
  waitEitherSTM l r =
    (map Left (waitSTM l)) `orElse` (map Right (waitSTM r))

  waitEither :: Async a -> Async b -> IO (Either a b)
  waitEither l r = atomically (waitEitherSTM l r)

  waitEitherSTM_:: Async a -> Async b -> STM ()
  waitEitherSTM_ l r =
    (void (waitSTM l)) `orElse` (void (waitSTM r))

  waitEither_ :: Async a -> Async b -> IO ()
  waitEither_ l r = atomically (waitEitherSTM_ l r)

  waitBothSTM :: Async a -> Async b -> STM (a, b)
  waitBothSTM l r = do
      a <- waitSTM l `orElse` (waitSTM r >> retry)
      b <- waitSTM r
      pure (a, b)

  waitBoth :: Async a -> Async b -> IO (a, b)
  waitBoth l r = atomically (waitBothSTM l r)

  waitBoth_ :: Async a -> Async b -> IO ()
  waitBoth_ l r = void (waitBoth l r)

  data AsyncCancelled = AsyncCancelled
    deriving (Show)

  instance Exception AsyncCancelled

  cancel :: Async a -> IO ()
  cancel a@(Async t _) = throwTo t AsyncCancelled <* waitCatch a

  uninterruptibleCancel :: Async a -> IO ()
  uninterruptibleCancel = uninterruptibleMask_ . cancel

  catchAll :: IO a -> (SomeException -> IO a) -> IO a
  catchAll = catch

  withAsyncUsing :: (IO () -> IO ThreadId)
    -> IO a -> (Async a -> IO b) -> IO b
  withAsyncUsing doFork = \ action inner -> do
    var <- newEmptyTMVarIO
    mask $ \ restore -> do
      t <- doFork (try (restore action) >>= atomically . putTMVar var)
      let a = Async t (readTMVar var)
      r <- restore (inner a) `catchAll` \ e -> do
        uninterruptibleCancel a
        throwIO e
      uninterruptibleCancel a
      pure r

  withAsync :: IO a -> (Async a -> IO b) -> IO b
  withAsync = withAsyncUsing forkIO
#-}

{-# COMPILE GHC Async = type Async #-}
{-# COMPILE GHC async = \ _ a -> async a #-}
{-# COMPILE GHC wait = \ _ a -> wait a #-}
{-# COMPILE GHC waitAny = \ _ as -> waitAny as #-}
{-# COMPILE GHC waitEither = \ _ _ a b -> waitEither a b #-}
{-# COMPILE GHC waitEither* = \ _ _ a b -> waitEither_ a b #-}
{-# COMPILE GHC waitBoth = \ _ _ a b -> waitBoth a b #-}
{-# COMPILE GHC waitBoth* = \ _ _ a b -> waitBoth_ a b #-}
{-# COMPILE GHC cancel = \ _ a -> cancel a #-}
{-# COMPILE GHC withAsync = \ _ _ a k -> withAsync a k #-}

-------------------------------------------------------------------------------
-- Concurrently
-------------------------------------------------------------------------------

record Concurrently (a : Set) : Set where
  constructor asConcurrently
  field runConcurrently : IO a

open Concurrently public

instance
  Functor-Concurrently : Functor Concurrently
  Functor-Concurrently .map f (asConcurrently a) = asConcurrently (map f a)

  Applicative-Concurrently : Applicative Concurrently
  Applicative-Concurrently .pure = asConcurrently <<< pure
  Applicative-Concurrently ._<*>_ (asConcurrently f) (asConcurrently x) =
    asConcurrently $ apply <$> concurrently f x

  Alternative-Concurrently : Alternative Concurrently
  Alternative-Concurrently .azero = let 2^32 = 4294967296 in
    asConcurrently $ forever $ threadDelay 2^32
  Alternative-Concurrently ._<|>_ (asConcurrently as) (asConcurrently bs) =
    asConcurrently $ either id id <$> race as bs

  Semigroup-Concurrently : {{Semigroup a}} -> Semigroup (Concurrently a)
  Semigroup-Concurrently ._<>_ x y = (| x <> y |)

  Monoid-Concurrently : {{Monoid a}} -> Monoid (Concurrently a)
  Monoid-Concurrently .mempty = pure mempty

mapConcurrently : {{Traversable t}} -> (a -> IO b) -> t a -> IO (t b)
mapConcurrently f = runConcurrently <<< traverse (asConcurrently <<< f)

mapConcurrently* : {{Foldable f}} -> (a -> IO b) -> f a -> IO Unit
mapConcurrently* f = runConcurrently <<< foldMap (asConcurrently <<< ignore <<< f)

replicateConcurrently : Nat -> IO a -> IO (List a)
replicateConcurrently cnt =
  runConcurrently <<< sequence <<< List.replicate cnt <<< asConcurrently

replicateConcurrently* : Nat -> IO a -> IO Unit
replicateConcurrently* cnt =
  runConcurrently <<< fold <<< List.replicate cnt <<< asConcurrently <<< ignore
