module Control.Monad.List.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Error.Class
open import Control.Monad.IO.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class
open import Data.Monoid.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s w : Type
    f m n : Type -> Type

-------------------------------------------------------------------------------
-- ListT
-------------------------------------------------------------------------------

record ListT (m : Type -> Type) (a : Type) : Type where
  constructor asListT
  field runListT : m r -> (a -> m r -> m r) -> m r

open ListT public

module _ {{_ : Monad m}} where

  nilListT : ListT m a
  nilListT = asListT \ n _ -> n

  consListT : a -> ListT m a -> ListT m a
  consListT x xs = asListT \ n c -> c x (runListT xs n c)

  singletonListT : a -> ListT m a
  singletonListT x = consListT x nilListT

  toListT : {{_ : Foldable f}} -> f a -> ListT m a
  toListT xs = foldr consListT xs nilListT

  fromListT : ListT m a -> m (List a)
  fromListT m = runListT m (pure []) \ where
    x m -> do
      xs <- m
      pure (x :: xs)

  foldListT : (a -> m b -> m b) -> m b -> ListT m a -> m b
  foldListT c n xs = runListT xs n c

instance
  Semigroup-ListT : {{Monad m}} -> Semigroup (ListT m a)
  Semigroup-ListT ._<>_ xs ys = asListT \ n c -> runListT xs (runListT ys n c) c

  Monoid-ListT : {{Monad m}} -> Monoid (ListT m a)
  Monoid-ListT .mempty = nilListT

  Functor-ListT : {{Monad m}} -> Functor (ListT m)
  Functor-ListT .map f xs = asListT \ n c -> runListT xs n \ h t -> c (f h) t

  Applicative-ListT : {{Monad m}} -> Applicative (ListT m)
  Applicative-ListT .pure = singletonListT
  Applicative-ListT ._<*>_ fs xs = asListT \ where
    n c -> runListT fs n \ h t -> runListT (map h xs) n c

  Monad-ListT : {{Monad m}} -> Monad (ListT m)
  Monad-ListT ._>>=_ xs k = asListT \ where
    n c -> runListT xs n \ h t -> runListT (k h) n c

  Alternative-ListT : {{Monad m}} -> Alternative (ListT m)
  Alternative-ListT .azero = mempty
  Alternative-ListT ._<|>_ = _<>_

  MonadTrans-ListT : MonadTrans ListT
  MonadTrans-ListT .lift m = asListT \ n c -> m >>= flip c n

  MonadIO-ListT : {{MonadIO m}} -> MonadIO (ListT m)
  MonadIO-ListT .liftIO = lift <<< liftIO

  MonadReader-ListT : {{MonadReader r m}} -> MonadReader r (ListT m)
  MonadReader-ListT .ask = lift ask

  MonadState-ListT : {{MonadState s m}} -> MonadState s (ListT m)
  MonadState-ListT .state = lift <<< state

  MonadWriter-ListT : {{MonadWriter w m}}
    -> MonadWriter w (ListT m)
  MonadWriter-ListT .tell = lift <<< tell

  MonadError-ListT : {{MonadError e m}} -> MonadError e (ListT m)
  MonadError-ListT .throwError = lift <<< throwError