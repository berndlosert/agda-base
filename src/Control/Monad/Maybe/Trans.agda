{-# OPTIONS --type-in-type #-}

module Control.Monad.Maybe.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Monad.IO.Class
open import Control.Monad.Trans.Class
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    m n : Type -> Type

-------------------------------------------------------------------------------
-- MaybeT
-------------------------------------------------------------------------------

abstract
  MaybeT : (m : Type -> Type) (a : Type) -> Type
  MaybeT m a = m (Maybe a)

  mkMaybeT : m (Maybe a) -> MaybeT m a
  mkMaybeT = id

  runMaybeT : MaybeT m a -> m (Maybe a)
  runMaybeT = id

mapMaybeT : (m (Maybe a) -> n (Maybe b)) -> MaybeT m a -> MaybeT n b
mapMaybeT f = mkMaybeT <<< f <<< runMaybeT

hoistMaybeT : {{Applicative m}} -> Maybe b -> MaybeT m b
hoistMaybeT = mkMaybeT <<< pure

instance
  Functor-MaybeT : {{Functor m}} -> Functor (MaybeT m)
  Functor-MaybeT .map f = mkMaybeT <<< map (map f) <<< runMaybeT

  Foldable-MaybeT : {{Foldable m}} -> Foldable (MaybeT m)
  Foldable-MaybeT .foldr {a = a} {b = b} f z = foldr go z <<< runMaybeT
    where
      go : Maybe a -> b -> b
      go Nothing y = y
      go (Just x) y = f x y

  Traversable-MaybeT : {{Traversable m}} -> Traversable (MaybeT m)
  Traversable-MaybeT .traverse f m = mkMaybeT <$> traverse (traverse f) (runMaybeT m)

  Applicative-MaybeT : {{Monad m}} -> Applicative (MaybeT m)
  Applicative-MaybeT .pure = mkMaybeT <<< pure <<< pure
  Applicative-MaybeT ._<*>_ fs xs = mkMaybeT do
    f <- runMaybeT fs
    x <- runMaybeT xs
    pure (f <*> x)

  Alternative-MaybeT : {{Monad m}} -> Alternative (MaybeT m)
  Alternative-MaybeT .empty = mkMaybeT (pure Nothing)
  Alternative-MaybeT ._<|>_ l r = mkMaybeT do
    x <- runMaybeT l
    case x of \ where
      Nothing -> runMaybeT r
      (Just _) -> pure x

  Monad-MaybeT : {{Monad m}} -> Monad (MaybeT m)
  Monad-MaybeT ._>>=_ m k = mkMaybeT do
    x <- runMaybeT m
    case x of \ where
      Nothing -> pure Nothing
      (Just y) -> runMaybeT (k y)

  MonadTrans-MaybeT : MonadTrans MaybeT
  MonadTrans-MaybeT .lift = mkMaybeT <<< map Just

  MonadIO-MaybeT : {{MonadIO m}} -> MonadIO (MaybeT m)
  MonadIO-MaybeT .liftIO = lift <<< liftIO
