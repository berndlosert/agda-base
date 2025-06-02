open import Prelude

open import Control.Monad.Either.Trans
open import Control.Monad.Error.Class
open import Control.Monad.List.Trans
open import Control.Monad.State.Class
open import System.IO

variable
  a e : Type
  m : Type -> Type


decr : {{MonadState Nat m}} -> {{MonadError Unit m}} -> m Unit
decr = caseM get \ where
  0 -> throwError tt
  (suc n) -> put n

doubleDecr : {{MonadState Nat m}} -> m Unit
doubleDecr = eitherT pure (const (put 100)) (decr >> decr)

tripleDecr' : {{MonadState Nat m}} -> {{MonadError Unit m}} -> m Unit
tripleDecr' {m} = decr >> handler (runEitherT (decr >> decr))
  where
    handler : m (Either Unit Unit) -> m Unit
    handler m = caseM m \ where
      (left _) -> pure tt
      (right _) -> put 100