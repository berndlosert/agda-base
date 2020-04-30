{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont where

open import Prelude

open import Control.Monad.Cont.Trans

private variable A B R R' : Set

Cont : Set -> Set -> Set
Cont R A = ContT R Identity A

aCont : ((A -> R) -> R) -> Cont R A
aCont f = aContT (λ c -> anIdentity (f (runIdentity ∘ c)))

runCont : Cont R A -> (A -> R) -> R
runCont m k = runIdentity (runContT m (anIdentity ∘ k))

evalCont : Cont R R -> R
evalCont m = runIdentity (evalContT m)

mapCont : (R -> R) -> Cont R A -> Cont R A
mapCont f = mapContT (map f)

withCont : ((B -> R) -> (A -> R)) -> Cont R A -> Cont R B
withCont f = withContT ((anIdentity ∘_) ∘ f ∘ (runIdentity ∘_))

reset : Cont R R -> Cont R' R
reset = resetT

shift : ((A -> R) -> Cont R R) -> Cont R A
shift f = shiftT (f ∘ (runIdentity ∘_))
