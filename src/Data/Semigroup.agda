module Data.Semigroup where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Agda.Builtin.String using ()
open import Data.Functor.Const using (Const; asConst; getConst)
open import Data.Functor.Identity using (Identity; asIdentity; runIdentity)
open import Data.Nat.Positive using (Nat1; suc)
open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Semigroup
-------------------------------------------------------------------------------

record Semigroup (a : Type) : Type where
  infixr 5 _<>_
  field _<>_ : a -> a -> a

  stimes : Nat1 -> a -> a
  stimes (suc n) x = applyN (x <>_) n x

open Semigroup {{...}} public

instance
  Semigroup-Void : Semigroup Void
  Semigroup-Void ._<>_ = \ ()

  Semigroup-Unit : Semigroup Unit
  Semigroup-Unit ._<>_ tt tt = tt

  Semigroup-Ordering : Semigroup Ordering
  Semigroup-Ordering ._<>_ less _ = less
  Semigroup-Ordering ._<>_ equal y = y
  Semigroup-Ordering ._<>_ greater _ = greater

  Semigroup-String : Semigroup String
  Semigroup-String ._<>_ = Agda.Builtin.String.primStringAppend

  Semigroup-Function : {{Semigroup b}} -> Semigroup (a -> b)
  Semigroup-Function ._<>_ f g x = f x <> g x

  Semigroup-Identity : {{Semigroup a}} -> Semigroup (Identity a)
  Semigroup-Identity {a} ._<>_ x y = asIdentity (runIdentity x <> runIdentity y)

  Semigroup-Const : {{Semigroup a}} -> Semigroup (Const a b)
  Semigroup-Const ._<>_ x y = asConst (getConst x <> getConst y)

  Semigroup-Maybe : {{Semigroup a}} -> Semigroup (Maybe a)
  Semigroup-Maybe ._<>_ nothing x = x
  Semigroup-Maybe ._<>_ x nothing = x
  Semigroup-Maybe ._<>_ (just x) (just y) = just (x <> y)

  Semigroup-List : Semigroup (List a)
  Semigroup-List ._<>_ [] ys = ys
  Semigroup-List ._<>_ (x :: xs) ys = x :: (xs <> ys)

  Semigroup-Either : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Either a b)
  Semigroup-Either ._<>_ (left _) x = x
  Semigroup-Either ._<>_ x _ = x

  Semigroup-Tuple : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Tuple a b)
  Semigroup-Tuple ._<>_ (x , y) (w , z) = (x <> w , y <> z)
