module Control.Applicative.FreeAp where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    f g : Type -> Type

-------------------------------------------------------------------------------
-- FreeAp
-------------------------------------------------------------------------------

data FreeAp (f : Type -> Type) (b : Type) : Type where
  Pure : b -> FreeAp f b
  Ap : FreeAp f (a -> b) -> f a -> FreeAp f b

liftFreeAp : f a -> FreeAp f a
liftFreeAp x = Ap (Pure id) x

retractFreeAp : {{Applicative f}} -> FreeAp f a -> f a
retractFreeAp (Pure x) = pure x
retractFreeAp (Ap f x) = retractFreeAp f <*> x

hoistFreeAp : (forall {a} -> f a -> g a) -> FreeAp f b -> FreeAp g b
hoistFreeAp t (Pure x) = Pure x
hoistFreeAp t (Ap f x) = Ap (hoistFreeAp t f) (t x)

runFreeAp : {{Applicative g}} -> (forall {a} -> f a -> g a) -> FreeAp f b -> g b
runFreeAp t = \ where
  (Pure x) -> pure x
  (Ap f x) -> runFreeAp t f <*> t x

instance
  Functor-FreeAp : Functor (FreeAp f)
  Functor-FreeAp .map f = \ where
    (Pure x) -> Pure (f x)
    (Ap g x) -> Ap (map (f <<<_) g) x

  Applicative-FreeAp : Applicative (FreeAp f)
  Applicative-FreeAp ._<*>_ f x = case f \ where
    (Pure g) -> map g x
    (Ap g y) -> Ap (map flip g <*> x) y
  Applicative-FreeAp .pure = Pure