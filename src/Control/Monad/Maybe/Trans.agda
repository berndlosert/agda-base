module Control.Monad.Maybe.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Error.Class
open import Control.Monad.IO.Class
open import Control.Monad.Trans.Class
open import Data.Monoid.Foldable
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
    a b e : Type
    m n : Type -> Type

-------------------------------------------------------------------------------
-- MaybeT
-------------------------------------------------------------------------------

record MaybeT (m : Type -> Type) (a : Type) : Type where
  constructor asMaybeT
  field runMaybeT : m (Maybe a)

open MaybeT public

mapMaybeT : (m (Maybe a) -> n (Maybe b)) -> MaybeT m a -> MaybeT n b
mapMaybeT f = asMaybeT <<< f <<< runMaybeT

hoistMaybe : {{Applicative m}} -> Maybe b -> MaybeT m b
hoistMaybe = asMaybeT <<< pure

fromMaybeT : {{Monad m}} -> MaybeT m a -> m a -> m a
fromMaybeT x y = runMaybeT x >>= maybe y pure

instance
  Functor-MaybeT : {{Functor m}} -> Functor (MaybeT m)
  Functor-MaybeT .map f = asMaybeT <<< map (map f) <<< runMaybeT

  Foldable-MaybeT : {{Foldable m}} -> Foldable (MaybeT m)
  Foldable-MaybeT .foldMap f = foldMap (foldMap f) <<< runMaybeT

  Traversable-MaybeT : {{Traversable m}} -> Traversable (MaybeT m)
  Traversable-MaybeT .traverse f m =
    asMaybeT <$> traverse (traverse f) (runMaybeT m)

  Applicative-MaybeT : {{Monad m}} -> Applicative (MaybeT m)
  Applicative-MaybeT .pure = asMaybeT <<< pure <<< pure
  Applicative-MaybeT ._<*>_ fs xs = asMaybeT do
    f <- runMaybeT fs
    x <- runMaybeT xs
    pure (f <*> x)

  Alternative-MaybeT : {{Monad m}} -> Alternative (MaybeT m)
  Alternative-MaybeT .azero = asMaybeT (pure nothing)
  Alternative-MaybeT ._<|>_ l r = asMaybeT do
    res <- runMaybeT l
    case res \ where
      nothing -> runMaybeT r
      (just _) -> pure res

  Monad-MaybeT : {{Monad m}} -> Monad (MaybeT m)
  Monad-MaybeT ._>>=_ m k = asMaybeT $
    caseM (runMaybeT m) \ where
      nothing -> pure nothing
      (just x) -> runMaybeT (k x)

  MonadTrans-MaybeT : MonadTrans MaybeT
  MonadTrans-MaybeT .lift = asMaybeT <<< map just

  MonadIO-MaybeT : {{MonadIO m}} -> MonadIO (MaybeT m)
  MonadIO-MaybeT .liftIO = lift <<< liftIO

  MonadError-MaybeT : {{MonadError e m}} -> MonadError e (MaybeT m)
  MonadError-MaybeT .throwError = lift <<< throwError
