module Control.Concurrent.Async where

open import Prelude

open import Control.Concurrent
open import Data.Time.Units

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
  waitAny : List (Async a) -> IO (Async a * a)
  waitEither : Async a -> Async b -> IO (a + b)
  waitEither! : Async a -> Async b -> IO Unit
  waitBoth : Async a -> Async b -> IO (a * b)
  waitBoth! : Async a -> Async b -> IO Unit
  cancel : Async a -> IO Unit
  withAsync : IO a -> (Async a -> IO b) -> IO b

race : IO a -> IO b -> IO (a + b)
race left right =
  withAsync left λ a ->
  withAsync right λ b ->
  waitEither a b

race! : IO a -> IO b -> IO Unit
race! left right =
  withAsync left λ a ->
  withAsync right λ b ->
  waitEither! a b

concurrently : IO a -> IO b -> IO (a * b)
concurrently left right =
  withAsync left λ a ->
  withAsync right λ b ->
  waitBoth a b

concurrently! : IO a -> IO b -> IO Unit
concurrently! left right = void (concurrently left right)

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
      doFork $ try (restore action) >>= atomically . putTMVar var
    return (Async t (readTMVar var))

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
     either throwSTM return r

  wait :: Async a -> IO a
  wait = tryAgain . atomically . waitSTM
    where tryAgain f = f `catch` (\ BlockedIndefinitelyOnSTM -> f)

  waitAnySTM :: [Async a] -> STM (Async a, a)
  waitAnySTM asyncs =
      foldr orElse retry $
        map (\ a -> do r <- waitSTM a; return (a, r)) asyncs

  waitAny :: [Async a] -> IO (Async a, a)
  waitAny = atomically . waitAnySTM

  waitEitherSTM :: Async a -> Async b -> STM (Either a b)
  waitEitherSTM left right =
    (Left <$> waitSTM left) `orElse` (Right <$> waitSTM right)

  waitEither :: Async a -> Async b -> IO (Either a b)
  waitEither left right = atomically (waitEitherSTM left right)

  waitEitherSTM_:: Async a -> Async b -> STM ()
  waitEitherSTM_ left right =
    (void $ waitSTM left) `orElse` (void $ waitSTM right)

  waitEither_ :: Async a -> Async b -> IO ()
  waitEither_ left right = atomically (waitEitherSTM_ left right)

  waitBothSTM :: Async a -> Async b -> STM (a, b)
  waitBothSTM left right = do
      a <- waitSTM left `orElse` (waitSTM right >> retry)
      b <- waitSTM right
      return (a, b)

  waitBoth :: Async a -> Async b -> IO (a, b)
  waitBoth left right = atomically (waitBothSTM left right)

  waitBoth_ :: Async a -> Async b -> IO ()
  waitBoth_ left right = void $ waitBoth left right

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
      t <- doFork $ try (restore action) >>= atomically . putTMVar var
      let a = Async t (readTMVar var)
      r <- restore (inner a) `catchAll` \ e -> do
        uninterruptibleCancel a
        throwIO e
      uninterruptibleCancel a
      return r

  withAsync :: IO a -> (Async a -> IO b) -> IO b
  withAsync = withAsyncUsing forkIO
#-}

{-# COMPILE GHC Async = type Async #-}
{-# COMPILE GHC async = \ _ a -> async a #-}
{-# COMPILE GHC wait = \ _ a -> wait a #-}
{-# COMPILE GHC waitAny = \ _ as -> waitAny as #-}
{-# COMPILE GHC waitEither = \ _ _ a b -> waitEither a b #-}
{-# COMPILE GHC waitEither! = \ _ _ a b -> waitEither_ a b #-}
{-# COMPILE GHC waitBoth = \ _ _ a b -> waitBoth a b #-}
{-# COMPILE GHC waitBoth! = \ _ _ a b -> waitBoth_ a b #-}
{-# COMPILE GHC cancel = \ _ a -> cancel a #-}
{-# COMPILE GHC withAsync = \ _ _ a k -> withAsync a k #-}

-------------------------------------------------------------------------------
-- Concurrently
-------------------------------------------------------------------------------

record Concurrently (a : Set) : Set where
  constructor Concurrently:
  field runConcurrently : IO a

open Concurrently public

instance
  Functor-Concurrently : Functor Concurrently
  Functor-Concurrently .map f (Concurrently: a) = Concurrently: (map f a)

  Applicative-Concurrently : Applicative Concurrently
  Applicative-Concurrently .pure = Concurrently: ∘ pure
  Applicative-Concurrently ._<*>_ (Concurrently: f) (Concurrently: x) =
    Concurrently: (apply <$> concurrently f x)

  Alternative-Concurrently : Alternative Concurrently
  Alternative-Concurrently .empty =
    Concurrently: (forever $ threadDelay ((2 ^ 32) μsec))
  Alternative-Concurrently ._<|>_ (Concurrently: as) (Concurrently: bs) =
    Concurrently: (untag <$> race as bs)

  Semigroup-Concurrently : {{_ : Semigroup a}} -> Semigroup (Concurrently a)
  Semigroup-Concurrently ._<>_ x y = (| _<>_ x y |)

  Monoid-Concurrently : {{_ : Monoid a}} -> Monoid (Concurrently a)
  Monoid-Concurrently .neutral = pure neutral

mapConcurrently : {{_ : Traversable t}} -> (a -> IO b) -> t a -> IO (t b)
mapConcurrently f = runConcurrently ∘ traverse (Concurrently: ∘ f)

mapConcurrently! : {{_ : Foldable f}} -> (a -> IO b) -> f a -> IO Unit
mapConcurrently! f = runConcurrently ∘ foldMap (Concurrently: ∘ void ∘ f)

replicateConcurrently : Nat -> IO a -> IO (List a)
replicateConcurrently cnt =
  runConcurrently ∘ sequence ∘ replicate cnt ∘ Concurrently:

replicateConcurrently! : Nat -> IO a -> IO Unit
replicateConcurrently! cnt =
  runConcurrently ∘ fold ∘ replicate cnt ∘ Concurrently: ∘ void
