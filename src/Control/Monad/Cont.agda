{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont where

open import Prelude

open import Control.Monad.Cont.Class public
open import Control.Monad.Cont.Trans public

private variable a b r r' : Set

Cont : Set -> Set -> Set
Cont r a = ContT r Identity a

cont: : ((a -> r) -> r) -> Cont r a
cont: f = ContT: λ c -> Identity: (f (runIdentity ∘ c))

runCont : Cont r a -> (a -> r) -> r
runCont m k = runIdentity (runContT m (Identity: ∘ k))

evalCont : Cont r r -> r
evalCont m = runIdentity (evalContT m)

mapCont : (r -> r) -> Cont r a -> Cont r a
mapCont f = mapContT (map f)

withCont : ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b
withCont f = withContT ((Identity: ∘_) ∘ f ∘ (runIdentity ∘_))

reset : Cont r r -> Cont r' r
reset = resetT

shift : ((a -> r) -> Cont r r) -> Cont r a
shift f = shiftT (f ∘ (runIdentity ∘_))
