{-# OPTIONS --type-in-type #-}

module Control.Monad.List.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Exception
open import Control.Monad.IO.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class
open import Data.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s w : Set
    f m n : Set -> Set

-------------------------------------------------------------------------------
-- ListT
-------------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
record ListT (m : Set -> Set) (a : Set) : Set where
  field runListT : m (Maybe (Pair a (ListT m a)))

open ListT public

module _ {{_ : Monad m}} where

  nilT : ListT m a
  nilT .runListT = pure nothing

  consT : a -> ListT m a -> ListT m a
  consT x xs .runListT = pure $ just (x , xs)

  singletonT : a -> ListT m a
  singletonT x = consT x nilT

  toListT : {{_ : Foldable f}} -> f a -> ListT m a
  toListT = foldr consT nilT

  {-# TERMINATING #-}
  foldListT : (b -> a -> m b) -> b -> ListT m a -> m b
  foldListT f b m = runListT m >>= \ where
    nothing -> pure b
    (just (x , xs)) -> f b x >>= \ b' -> foldListT f b' xs

  {-# TERMINATING #-}
  hoistListT : (forall {a} -> m a -> n a) -> ListT m b -> ListT n b
  hoistListT f m .runListT =
     (f <<< (map <<< map) (bimap id (hoistListT f)) <<< runListT) m

instance
  {-# TERMINATING #-}
  Semigroup-ListT : {{Monad m}} -> Semigroup (ListT m a)
  Semigroup-ListT ._<>_ l r .runListT = runListT l >>= \ where
    nothing -> runListT r
    (just (x , xs)) -> pure $ just (x , xs <> r)

  Monoid-ListT : {{Monad m}} -> Monoid (ListT m a)
  Monoid-ListT .mempty = nilT

  {-# TERMINATING #-}
  Functor-ListT : {{Monad m}} -> Functor (ListT m)
  Functor-ListT .map f m .runListT = runListT m >>= \ where
    nothing -> pure nothing
    (just (x , xs)) -> pure $ just (f x , map f xs)

  {-# TERMINATING #-}
  Applicative-ListT : {{Monad m}} -> Applicative (ListT m)
  Applicative-ListT .pure x .runListT = pure (just (x , mempty))
  Applicative-ListT ._<*>_ fs xs .runListT = runListT fs >>= \ where
    nothing -> pure nothing
    (just (f , fs')) -> runListT $ (map f xs) <> (fs' <*> xs)

  {-# TERMINATING #-}
  Monad-ListT : {{Monad m}} -> Monad (ListT m)
  Monad-ListT ._>>=_ m k .runListT = runListT m >>= \ where
    nothing -> pure nothing
    (just (x , xs)) -> runListT $ k x <> (xs >>= k)

  Alternative-ListT : {{Monad m}} -> Alternative (ListT m)
  Alternative-ListT .azero = mempty
  Alternative-ListT ._<|>_ = _<>_

  MonadTrans-ListT : MonadTrans ListT
  MonadTrans-ListT .lift m .runListT = map (just <<< (_, mempty)) m

  MonadIO-ListT : {{MonadIO m}} -> MonadIO (ListT m)
  MonadIO-ListT .liftIO = lift <<< liftIO

  MonadThrow-ListT : {{MonadThrow e m}} -> MonadThrow e (ListT m)
  MonadThrow-ListT .throw e .runListT = throw e

  MonadCatch-ListT : {{MonadCatch e m}} -> MonadCatch e (ListT m)
  MonadCatch-ListT .catch m handler .runListT =
    catch (runListT m) (runListT <<< handler)

  MonadReader-ListT : {{MonadReader r m}} -> MonadReader r (ListT m)
  MonadReader-ListT .ask = lift ask
  MonadReader-ListT .local f = hoistListT (local f)

  MonadState-ListT : {{MonadState s m}} -> MonadState s (ListT m)
  MonadState-ListT .state = lift <<< state

  {-# TERMINATING #-}
  MonadWriter-ListT : {{MonadWriter w m}}
    -> MonadWriter w (ListT m)
  MonadWriter-ListT .tell = lift <<< tell
  MonadWriter-ListT .listen m .runListT = runListT m >>= \ where
    nothing -> pure nothing
    (just (x , xs)) -> do
      (a , w) <- listen (pure x)
      pure $ just ((a , w) , listen xs)
  MonadWriter-ListT .pass m .runListT = runListT m >>= \ where
    nothing -> pure nothing
    (just ((x , f) , rest)) -> do
      a <- pass $ pure (x , f)
      pure $ just (a , pass rest)
