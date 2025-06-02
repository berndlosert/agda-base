module Control.Concurrent.Async where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Concurrent
open import Data.List as List using ()
open import Data.Monoid.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    f t : Type -> Type

-------------------------------------------------------------------------------
-- Async
-------------------------------------------------------------------------------

postulate
  Async : Type -> Type
  async : IO a -> IO (Async a)
  wait : Async a -> IO a
  waitAny : List (Async a) -> IO (Tuple (Async a) a)
  waitEither : Async a -> Async b -> IO (Either a b)
  waitEither' : Async a -> Async b -> IO Unit
  waitAll : Async a -> Async b -> IO (Tuple a b)
  waitAll' : Async a -> Async b -> IO Unit
  cancel : Async a -> IO Unit
  withAsync : IO a -> (Async a -> IO b) -> IO b
  race : IO a -> IO b -> IO (Either a b)
  race' : IO a -> IO b -> IO Unit
  concurrently : IO a -> IO b -> IO (Tuple a b)
  concurrently' : IO a -> IO b -> IO Unit

-------------------------------------------------------------------------------
-- Async FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Control.Concurrent.Async #-}
{-# COMPILE GHC Async = type Async #-}
{-# COMPILE GHC async = \ _ -> async #-}
{-# COMPILE GHC wait = \ _ -> wait #-}
{-# COMPILE GHC waitAny = \ _ -> waitAny #-}
{-# COMPILE GHC waitEither = \ _ _ -> waitEither #-}
{-# COMPILE GHC waitEither' = \ _ _ -> waitEither_ #-}
{-# COMPILE GHC waitAll = \ _ _ -> waitAll #-}
{-# COMPILE GHC cancel = \ _ -> cancel #-}
{-# COMPILE GHC withAsync = \ _ _ -> withAsync #-}
{-# COMPILE GHC race = \ _ _ -> race #-}
{-# COMPILE GHC race' = \ _ _ -> race_ #-}
{-# COMPILE GHC concurrently = \ _ _ -> concurrently #-}
{-# COMPILE GHC concurrently' = \ _ _ -> concurrently_ #-}

-------------------------------------------------------------------------------
-- Concurrently
-------------------------------------------------------------------------------

postulate
  Concurrently : Type -> Type
  asConcurrently : IO a -> Concurrently a
  runConcurrently : Concurrently a -> IO a

instance
  Functor-Concurrently : Functor Concurrently
  Functor-Concurrently .map f x = asConcurrently (f <$> runConcurrently x)

  Applicative-Concurrent : Applicative Concurrently
  Applicative-Concurrent .pure = asConcurrently <<< pure
  Applicative-Concurrent ._<*>_ f x = asConcurrently do
    (f , x) <- concurrently (runConcurrently f) (runConcurrently x)
    pure (f x)

  Alternative-Concurrent : Alternative Concurrently
  Alternative-Concurrent .azero = let 2^32 = 4294967296 in
    asConcurrently (forever (threadDelay 2^32))
  Alternative-Concurrent ._<|>_ xs ys =
    asConcurrently (uneither <$> race (runConcurrently xs) (runConcurrently ys))

  Semigroup-Concurrent : {{Semigroup a}} -> Semigroup (Concurrently a)
  Semigroup-Concurrent ._<>_ x y = (| x <> y |)

  Monoid-Concurrent : {{Monoid a}} -> Monoid (Concurrently a)
  Monoid-Concurrent .mempty = pure mempty

mapConcurrently : {{Traversable t}} -> (a -> IO b) -> t a -> IO (t b)
mapConcurrently f = runConcurrently <<< traverse (asConcurrently <<< f)

mapConcurrently! : {{Foldable f}} -> (a -> IO b) -> f a -> IO Unit
mapConcurrently! f = runConcurrently <<< foldMap (asConcurrently <<< map ! <<< f)

replicateConcurrently : Nat -> IO a -> IO (List a)
replicateConcurrently cnt =
  runConcurrently <<< sequence <<< List.replicate cnt <<< asConcurrently

replicateConcurrently! : Nat -> IO a -> IO Unit
replicateConcurrently! cnt =
  runConcurrently <<< fold <<< List.replicate cnt <<< asConcurrently <<< map !

{-# COMPILE GHC Concurrently = type Concurrently #-}
{-# COMPILE GHC asConcurrently = \ _ -> Concurrently #-}
{-# COMPILE GHC runConcurrently = \ _ -> runConcurrently #-}