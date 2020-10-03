{-# OPTIONS --type-in-type #-}

module Control.Monad.Morph where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Trans.Class

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    m n : Set -> Set
    t : (Set -> Set) -> Set -> Set

-------------------------------------------------------------------------------
-- MFunctor
-------------------------------------------------------------------------------

record MFunctor (t : (Set -> Set) -> Set -> Set) : Set where
  field
    hoist : {{_ : Monad m}} {{_ : Monad n}}
      -> (forall {a} -> m a -> n a) -> t m b -> t n b

open MFunctor {{...}} public

-------------------------------------------------------------------------------
-- MMonad
-------------------------------------------------------------------------------

record MMonad (t : (Set -> Set) -> Set -> Set) : Set where
  field
    overlap {{Mfunctor-super}} : MFunctor t
    overlap {{MonadTrans-super}} : MonadTrans t
    embed : {{_ : Monad m}} {{_ : Monad n}}
      -> (forall {a} -> m a -> t n a) -> t m b -> t n b

open MMonad {{...}} public

generalize : {{_ : Monad m}} -> Identity a -> m a
generalize (Identity: x) = return x

squash : {{_ : Monad m}} {{_ : MMonad t}} -> t (t m) a -> t m a
squash = embed id
