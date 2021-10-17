{-# OPTIONS --type-in-type #-}

open import Prelude
  hiding (Nat)
  hiding (zero)
  hiding (suc)
  hiding (List)
  hiding ([])
  hiding (_::_)

open import Control.Recursion

variable
  a : Set

NatS : Signature
NatS .Symbol = Bool -- false means zero, true means suc
NatS .Arity false = Void
NatS .Arity true = Unit

Nat = Fix NatS

zero : Nat
zero = sup false absurd

suc : Nat -> Nat
suc n = sup true (const n)

ListS : Set -> Signature
ListS a .Symbol = Maybe a -- nothing means [], just x means x ::_
ListS a .Arity nothing = Void
ListS a .Arity (just _) = Unit

List : Set -> Set
List a = Fix (ListS a)

[] : List a
[] = sup nothing absurd

infixr 5 _::_
_::_ : a -> List a -> List a
x :: (sup nothing arg) = sup (just x) (const [])
x :: (sup (just y) arg) = sup (just x) (\ _ -> let ys = arg tt in y :: ys)

length : List a -> Nat
length {a} = foldFix alg
  where
    alg : Algebra (ListS a) Nat
    alg (anOperation nothing _) = zero
    alg (anOperation (just _) arg) = suc (arg tt)

one = suc zero
two = suc one
three = suc two

test : length (one :: two :: three :: []) === three
test = refl
