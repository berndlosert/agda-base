module Control.Monad.Morph where

open import Prelude

open import Control.Monad.Trans.Class

private
  variable
    m n : Set -> Set
    t : (Set -> Set) -> Set -> Set

--------------------------------------------------------------------------------
-- MFunctor
--------------------------------------------------------------------------------

record MFunctor (t : (Set -> Set) -> Set -> Set) : Set where
  field hoist : {{_ : Monad m}} {{_ : Monad n}} -> (m ~> n) -> t m ~> t n

open MFunctor {{...}} public

--------------------------------------------------------------------------------
-- MMonad
--------------------------------------------------------------------------------

record MMonad (t : (Set -> Set) -> Set -> Set) : Set where
  field
    overlap {{mfunctor}} : MFunctor t
    overlap {{monadtrans}} : MonadTrans t
    embed : {{_ : Monad m}} {{_ : Monad n}} -> (m ~> t n) -> t m ~> t n

open MMonad {{...}} public

generalize : {{_ : Monad m}} -> Identity ~> m
generalize (Identity: x) = return x

squash : {{_ : Monad m}} {{_ : MMonad t}} -> t (t m) ~> t m
squash = embed id
