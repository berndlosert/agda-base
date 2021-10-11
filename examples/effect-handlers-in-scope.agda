{-# OPTIONS --type-in-type #-}

open import Prelude

open import Control.Exception
open import Control.Monad.Either.Trans
open import Control.Monad.State.Trans
open import Data.Functor.Identity

variable
  m : Set -> Set

decr : {{MonadState Nat m}} -> {{MonadThrow Unit m}} -> m Unit
decr = do
  n <- get
  case n of \ where
    0 -> throw tt
    (suc m) -> put m

interpret1 : EitherT Unit (StateT Nat Identity) Unit
  -> Pair Nat (Either Unit Unit)
interpret1 = runIdentity <<< flip runStateT 0 <<< runEitherT

test1 = interpret1 decr === (0 , left tt)
