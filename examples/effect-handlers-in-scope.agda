open import Control.Monad using (Monad; caseM)
open import Control.Monad.Either.Trans
open import Control.Monad.Error.Class
open import Control.Monad.Instances using (Monad-Identity)
open import Control.Monad.State.Trans
open import Control.Semigroupoid using (_<<<_)
open import Data.Functor.Identity using (Identity; runIdentity)
open import Prelude

variable
  m : Type -> Type

decr : {{MonadState Nat m}} -> {{MonadError Unit m}} -> m Unit
decr = caseM get \ where
  0 -> throwError tt
  (suc n) -> put n

interpret1 : EitherT Unit (StateT Nat Identity) Unit
  -> Tuple Nat (Either Unit Unit)
interpret1 = runIdentity <<< flip runStateT 0 <<< runEitherT

test1 = interpret1 decr === (0 , left tt)
