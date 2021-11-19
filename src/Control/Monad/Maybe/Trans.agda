module Control.Monad.Maybe.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Error.Class
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
    a b e : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- MaybeT
-------------------------------------------------------------------------------

record MaybeT (m : Set -> Set) (a : Set) : Set where
  constructor aMaybeT
  field runMaybeT : m (Maybe a)

open MaybeT public

mapMaybeT : (m (Maybe a) -> n (Maybe b)) -> MaybeT m a -> MaybeT n b
mapMaybeT f = aMaybeT <<< f <<< runMaybeT

hoistMaybeT : {{Applicative m}} -> Maybe b -> MaybeT m b
hoistMaybeT = aMaybeT <<< pure

instance
  Functor-MaybeT : {{Functor m}} -> Functor (MaybeT m)
  Functor-MaybeT .map f = aMaybeT <<< map (map f) <<< runMaybeT

  Foldable-MaybeT : {{Foldable m}} -> Foldable (MaybeT m)
  Foldable-MaybeT .foldr {a = a} {b = b} step init =
      foldr step' init  <<< runMaybeT
    where
      step' : Maybe a -> b -> b
      step' nothing acc = acc
      step' (just x) acc = step x acc

  Traversable-MaybeT : {{Traversable m}} -> Traversable (MaybeT m)
  Traversable-MaybeT .traverse f m =
    aMaybeT <$> traverse (traverse f) (runMaybeT m)

  Applicative-MaybeT : {{Monad m}} -> Applicative (MaybeT m)
  Applicative-MaybeT .pure = aMaybeT <<< pure <<< pure
  Applicative-MaybeT ._<*>_ fs xs = aMaybeT do
    f <- runMaybeT fs
    x <- runMaybeT xs
    pure (f <*> x)

  Alternative-MaybeT : {{Monad m}} -> Alternative (MaybeT m)
  Alternative-MaybeT .azero = aMaybeT (pure nothing)
  Alternative-MaybeT ._<|>_ l r = aMaybeT do
    res <- runMaybeT l
    case res of \ where
      nothing -> runMaybeT r
      (just _) -> pure res

  Monad-MaybeT : {{Monad m}} -> Monad (MaybeT m)
  Monad-MaybeT ._>>=_ m k = aMaybeT do
    res <- runMaybeT m
    case res of \ where
      nothing -> pure nothing
      (just x) -> runMaybeT (k x)

  MonadTrans-MaybeT : MonadTrans MaybeT
  MonadTrans-MaybeT .lift = aMaybeT <<< map just

  MonadIO-MaybeT : {{MonadIO m}} -> MonadIO (MaybeT m)
  MonadIO-MaybeT .liftIO = lift <<< liftIO

  MonadError-MaybeT : {{MonadError e m}} -> MonadError e (MaybeT m)
  MonadError-MaybeT .throwError = lift <<< throwError
  MonadError-MaybeT ._catchError_ m h = aMaybeT $
    (runMaybeT m) catchError (runMaybeT <<< h)
