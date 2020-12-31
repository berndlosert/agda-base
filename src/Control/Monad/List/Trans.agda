{-# OPTIONS --type-in-type #-}

module Control.Monad.List.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Monad.Except.Class
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
  constructor ListT:
  field unconsT : m (Maybe (a * ListT m a))

open ListT public

module _ {{_ : Monad m}} where

  nilT : ListT m a
  nilT = ListT: $ return Nothing

  consT : a -> ListT m a -> ListT m a
  consT x xs = ListT: $ return $ Just (x , xs)

  singletonT : a -> ListT m a
  singletonT x = consT x nilT

  toListT : {{_ : Foldable f}} -> f a -> ListT m a
  toListT = foldr consT nilT

  {-# TERMINATING #-}
  foldListT : (b -> a -> m b) -> b -> ListT m a -> m b
  foldListT f b (ListT: m) = m >>= \ where
    Nothing -> return b
    (Just (x , xs)) -> f b x >>= \ b' -> foldListT f b' xs

  {-# TERMINATING #-}
  runListT : ListT m a -> m (List a)
  runListT (ListT: m) = m >>= \ where
    Nothing -> return []
    (Just (x , xs)) -> (| _::_ (return x) (runListT xs) |)

  {-# TERMINATING #-}
  hoistListT : (forall {a} -> m a -> n a) -> ListT m b -> ListT n b
  hoistListT f =
    ListT: <<< f <<< (map <<< map) (bimap id (hoistListT f)) <<< unconsT

instance
  {-# TERMINATING #-}
  Semigroup-ListT : {{_ : Monad m}} -> Semigroup (ListT m a)
  Semigroup-ListT ._<>_ (ListT: l) (ListT: r) = ListT: $ l >>= \ where
    Nothing -> r
    (Just (x , xs)) -> return $ Just (x , xs <> ListT: r)

  Monoid-ListT : {{_ : Monad m}} -> Monoid (ListT m a)
  Monoid-ListT .neutral = nilT

  {-# TERMINATING #-}
  Functor-ListT : {{_ : Monad m}} -> Functor (ListT m)
  Functor-ListT .map f (ListT: m) = ListT: $ m >>= \ where
    Nothing -> return Nothing
    (Just (x , xs)) -> return $ Just (f x , map f xs)

  {-# TERMINATING #-}
  Applicative-ListT : {{_ : Monad m}} -> Applicative (ListT m)
  Applicative-ListT .pure x = ListT: (return (Just (x , neutral)))
  Applicative-ListT ._<*>_ fs xs = ListT: $ unconsT fs >>= \ where
    Nothing -> return Nothing
    (Just (f , fs')) -> unconsT $ (map f xs) <> (fs' <*> xs)

  {-# TERMINATING #-}
  Monad-ListT : {{_ : Monad m}} -> Monad (ListT m)
  Monad-ListT ._>>=_ (ListT: m) k = ListT: $ m >>= \ where
    Nothing -> return Nothing
    (Just (x , xs)) -> unconsT $ k x <> (xs >>= k)

  Alternative-ListT : {{_ : Monad m}} -> Alternative (ListT m)
  Alternative-ListT .empty = neutral
  Alternative-ListT ._<|>_ = _<>_

  MonadTrans-ListT : MonadTrans ListT
  MonadTrans-ListT .lift = ListT: <<< map (\ x -> Just (x , neutral))

  MonadIO-ListT : {{_ : MonadIO m}} -> MonadIO (ListT m)
  MonadIO-ListT .liftIO = lift <<< liftIO

  MonadThrow-ListT : {{_ : MonadThrow e m}} -> MonadThrow e (ListT m)
  MonadThrow-ListT .throw = ListT: <<< throw

  MonadExcept-ListT : {{_ : MonadExcept e m}} -> MonadExcept e (ListT m)
  MonadExcept-ListT .catch m handler =
    ListT: (catch (unconsT m) (unconsT <<< handler))

  MonadReader-ListT : {{_ : MonadReader r m}} -> MonadReader r (ListT m)
  MonadReader-ListT .ask = lift ask
  MonadReader-ListT .local f = hoistListT (local f)

  MonadState-ListT : {{_ : MonadState s m}} -> MonadState s (ListT m)
  MonadState-ListT .state = lift <<< state

  {-# TERMINATING #-}
  MonadWriter-ListT : {{_ : MonadWriter w m}}
    -> MonadWriter w (ListT m)
  MonadWriter-ListT .tell = lift <<< tell
  MonadWriter-ListT .listen (ListT: m) = ListT: $ m >>= \ where
    Nothing -> return Nothing
    (Just (x , xs)) -> do
      (a , w) <- listen (return x)
      return $ Just ((a , w) , listen xs)
  MonadWriter-ListT .pass (ListT: m) = ListT: $ m >>= \ where
    Nothing -> return Nothing
    (Just ((x , f) , rest)) -> do
      a <- pass $ return (x , f)
      return $ Just (a , pass rest)
