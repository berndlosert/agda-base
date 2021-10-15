{-# OPTIONS --type-in-type #-}

module Control.Monad.Maybe.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
    a b : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- MaybeT
-------------------------------------------------------------------------------

record MaybeT (m : Set -> Set) (a : Set) : Set where
  constructor toMaybeT
  field runMaybeT : m (Maybe a)

open MaybeT public

mapMaybeT : (m (Maybe a) -> n (Maybe b)) -> MaybeT m a -> MaybeT n b
mapMaybeT f = toMaybeT <<< f <<< runMaybeT

hoistMaybeT : {{Applicative m}} -> Maybe b -> MaybeT m b
hoistMaybeT = toMaybeT <<< pure

instance
  Functor-MaybeT : {{Functor m}} -> Functor (MaybeT m)
  Functor-MaybeT .map f = toMaybeT <<< map (map f) <<< runMaybeT

  Foldable-MaybeT : {{Foldable m}} -> Foldable (MaybeT m)
  Foldable-MaybeT .foldr {a = a} {b = b} f z = foldr go z <<< runMaybeT
    where
      go : Maybe a -> b -> b
      go nothing y = y
      go (just x) y = f x y

  Traversable-MaybeT : {{Traversable m}} -> Traversable (MaybeT m)
  Traversable-MaybeT .traverse f m = toMaybeT <$> traverse (traverse f) (runMaybeT m)

  Applicative-MaybeT : {{Monad m}} -> Applicative (MaybeT m)
  Applicative-MaybeT .pure = toMaybeT <<< pure <<< pure
  Applicative-MaybeT ._<*>_ fs xs = toMaybeT do
    f <- runMaybeT fs
    x <- runMaybeT xs
    pure (f <*> x)

  Alternative-MaybeT : {{Monad m}} -> Alternative (MaybeT m)
  Alternative-MaybeT .azero = toMaybeT (pure nothing)
  Alternative-MaybeT ._<|>_ l r = toMaybeT do
    x <- runMaybeT l
    case x of \ where
      nothing -> runMaybeT r
      (just _) -> pure x

  Monad-MaybeT : {{Monad m}} -> Monad (MaybeT m)
  Monad-MaybeT ._>>=_ m k = toMaybeT do
    x <- runMaybeT m
    case x of \ where
      nothing -> pure nothing
      (just y) -> runMaybeT (k y)

  MonadTrans-MaybeT : MonadTrans MaybeT
  MonadTrans-MaybeT .lift = toMaybeT <<< map just

  MonadIO-MaybeT : {{MonadIO m}} -> MonadIO (MaybeT m)
  MonadIO-MaybeT .liftIO = lift <<< liftIO
