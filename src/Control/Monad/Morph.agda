{-# OPTIONS --type-in-type #-}

module Control.Monad.Morph where

open import Prelude

open import Control.Monad.Trans.Class

private
  variable
    M N : Set -> Set
    T : (Set -> Set) -> Set -> Set

--------------------------------------------------------------------------------
-- MFunctor
--------------------------------------------------------------------------------

record MFunctor (T : (Set -> Set) -> Set -> Set) : Set where
  field hoist : (M ~> N) -> T M ~> T N

open MFunctor {{...}} public

--------------------------------------------------------------------------------
-- MMonad
--------------------------------------------------------------------------------

record MMonad (T : (Set -> Set) -> Set -> Set) : Set where
  field
    {{mfunctor}} : MFunctor T
    {{monadtrans}} : MonadTrans T
    embed : {{_ : Monad N}} -> (M ~> T N) -> T M ~> T N

open MMonad {{...}} public

generalize : {{_ : Monad M}} -> Identity ~> M
generalize (identity: x) = return x

squash : {{_ : Monad M}} {{_ : MMonad T}} -> T (T M) ~> T M
squash = embed id
