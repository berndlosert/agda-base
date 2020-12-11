{-# OPTIONS --type-in-type #-}

module Control.Monad.List.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Monad.Except.Class
open import Control.Monad.IO.Class
open import Control.Monad.Morph
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- ListT
-------------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
record ListT (m : Set -> Set) (a : Set) : Set where
  constructor ListT:
  field uncons : m (Maybe (a * ListT m a))

open ListT public

instance
  {-# TERMINATING #-}
  Semigroup-ListT : {{_ : Monad m}} -> Semigroup (ListT m a)
  Semigroup-ListT ._<>_ (ListT: l) (ListT: r) = ListT: $ l >>= \ where
    Nothing -> r
    (Just (x , xs)) -> return (Just (x , xs <> ListT: r))

  Monoid-ListT : {{_ : Monad m}} -> Monoid (ListT m a)
  Monoid-ListT .mempty = ListT: (return Nothing)

  {-# TERMINATING #-}
  Functor-ListT : {{_ : Monad m}} -> Functor (ListT m)
  Functor-ListT .map f = ListT: <<< (map <<< map) (bimap f (map f)) <<< uncons

  {-# TERMINATING #-}
  Applicative-ListT : {{_ : Monad m}} -> Applicative (ListT m)
  Applicative-ListT .pure x = ListT: (return (Just (x , mempty)))
  Applicative-ListT ._<*>_ fs xs = ListT: $ uncons fs >>= \ where
    Nothing -> return Nothing
    (Just (f , fs')) -> uncons $ (map f xs) <> (fs' <*> xs)

  {-# TERMINATING #-}
  Monad-ListT : {{_ : Monad m}} -> Monad (ListT m)
  Monad-ListT ._>>=_ xs k = ListT: $ uncons xs >>= \ where
    Nothing -> return Nothing
    (Just (y , ys)) -> uncons $ k y <> (ys >>= k)

  Alternative-ListT : {{_ : Monad m}} -> Alternative (ListT m)
  Alternative-ListT .empty = mempty
  Alternative-ListT ._<|>_ = _<>_

  MonadTrans-ListT : MonadTrans ListT
  MonadTrans-ListT .lift = ListT: <<< map (\ x -> Just (x , mempty))

  MonadIO-ListT : {{_ : MonadIO m}} -> MonadIO (ListT m)
  MonadIO-ListT .liftIO = lift <<< liftIO

  {-# TERMINATING #-}
  MFunctor-ListT : MFunctor ListT
  MFunctor-ListT .hoist f =
    ListT: <<< f <<< (map <<< map) (bimap id (hoist f)) <<< uncons

  {-# TERMINATING #-}
  MMonad-ListT : MMonad ListT
  MMonad-ListT .embed f (ListT: m) = f m >>= \ where
    Nothing -> empty
    (Just (h , t)) -> ListT: (return (Just (h , embed f t)))

  MonadThrow-ListT : {{_ : MonadThrow e m}} -> MonadThrow e (ListT m)
  MonadThrow-ListT .throw = ListT: <<< throw

  MonadExcept-ListT : {{_ : MonadExcept e m}} -> MonadExcept e (ListT m)
  MonadExcept-ListT .catch m handler =
    ListT: (catch (uncons m) (uncons <<< handler))

  MonadReader-ListT : {{_ : MonadReader r m}} -> MonadReader r (ListT m)
  MonadReader-ListT .ask = lift ask
  MonadReader-ListT .local f = hoist (local f)

  MonadState-ListT : {{_ : MonadState s m}} -> MonadState s (ListT m)
  MonadState-ListT .state = lift <<< state
