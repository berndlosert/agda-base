{-# OPTIONS --type-in-type #-}

module Control.Monad.List.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception
open import Control.Monad.IO.Class
open import Control.Monad.Error.Class
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

  foldListT : (b -> a -> m b) -> b -> ListT m a -> m b
  foldListT = fix \ where
    go f b m -> do
      res <- runListT m
      case res of \ where
        nothing -> pure b
        (just (x , xs)) -> do
          b' <- f b x
          go f b' xs

  hoistListT : (forall {a} -> m a -> n a) -> ListT m b -> ListT n b
  hoistListT = fix \ where
    go f m .runListT ->
     (f <<< (map <<< map) (bimap id (go f)) <<< runListT) m

instance
  Semigroup-ListT : {{Monad m}} -> Semigroup (ListT m a)
  Semigroup-ListT ._<>_ = fix \ where
    go l r .runListT -> do
      res <- runListT l
      case res of \ where
        nothing -> runListT r
        (just (x , xs)) -> pure $ just (x , go xs r)

  Monoid-ListT : {{Monad m}} -> Monoid (ListT m a)
  Monoid-ListT .mempty = nilT

  Functor-ListT : {{Monad m}} -> Functor (ListT m)
  Functor-ListT .map = fix \ where
    go f m .runListT -> do
      res <- runListT m
      case res of \ where
        nothing -> pure nothing
        (just (x , xs)) -> pure $ just (f x , go f xs)

  Applicative-ListT : {{Monad m}} -> Applicative (ListT m)
  Applicative-ListT .pure x .runListT = pure (just (x , mempty))
  Applicative-ListT ._<*>_ = fix \ where
    go fs xs .runListT -> do
      res <- runListT fs
      case res of \ where
        nothing -> pure nothing
        (just (f , fs')) -> runListT $ (map f xs) <> (go fs' xs)

  Monad-ListT : {{Monad m}} -> Monad (ListT m)
  Monad-ListT ._>>=_ = fix \ where
    go m k .runListT -> do
      res <- runListT m
      case res of \ where
        nothing -> pure nothing
        (just (x , xs)) -> runListT $ k x <> (go xs k)

  Alternative-ListT : {{Monad m}} -> Alternative (ListT m)
  Alternative-ListT .azero = mempty
  Alternative-ListT ._<|>_ = _<>_

  MonadTrans-ListT : MonadTrans ListT
  MonadTrans-ListT .lift m .runListT = map (just <<< (_, mempty)) m

  MonadIO-ListT : {{MonadIO m}} -> MonadIO (ListT m)
  MonadIO-ListT .liftIO = lift <<< liftIO

  MonadThrow-ListT : {{MonadThrow m}} -> MonadThrow (ListT m)
  MonadThrow-ListT .throw e .runListT = throw e

  MonadCatch-ListT : {{MonadCatch m}} -> MonadCatch (ListT m)
  MonadCatch-ListT .catch m handler .runListT =
    catch (runListT m) (runListT <<< handler)

  MonadReader-ListT : {{MonadReader r m}} -> MonadReader r (ListT m)
  MonadReader-ListT .ask = lift ask
  MonadReader-ListT .local f = hoistListT (local f)

  MonadState-ListT : {{MonadState s m}} -> MonadState s (ListT m)
  MonadState-ListT .state = lift <<< state

  MonadWriter-ListT : {{MonadWriter w m}}
    -> MonadWriter w (ListT m)
  MonadWriter-ListT .tell = lift <<< tell
  MonadWriter-ListT .listen = fix \ where
    go m .runListT -> do
      res <- runListT m
      case res of \ where
        nothing -> pure nothing
        (just (x , xs)) -> do
          (a , w) <- listen (pure x)
          pure $ just ((a , w) , go xs)
  MonadWriter-ListT .pass = fix \ where
    go m .runListT -> do
      res <- runListT m
      case res of \ where
        nothing -> pure nothing
        (just ((x , f) , rest)) -> do
          a <- pass $ pure (x , f)
          pure $ just (a , go rest)

  MonadError-ListT : {{MonadError e m}} -> MonadError e (ListT m)
  MonadError-ListT .raiseError = lift <<< raiseError
  MonadError-ListT .handleError m h .runListT =
    handleError (runListT m) (runListT <<< h)
