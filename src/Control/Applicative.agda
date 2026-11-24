module Control.Applicative where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Control.Semigroupoid using (_<<<_)
open import Data.Functor using (Functor; map; _<$>_)
open import Data.Functor.Const using (Const; asConst; getConst)
open import Data.Functor.Identity using (Identity; asIdentity; runIdentity)
open import Data.Monoid using (Monoid; mempty)
open import Data.Semigroup using (_<>_)
open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Applicative
-------------------------------------------------------------------------------

record Applicative (f : Type -> Type) : Type where
  infixl 4 _<*>_
  field
    overlap {{Functor-super}} : Functor f
    _<*>_ : f (a -> b) -> f a -> f b
    pure : a -> f a

  infixl 4 _*>_
  _*>_ : f a -> f b -> f b
  x *> y = (| (flip const) x y |)

  infixl 4 _<*_
  _<*_ : f a -> f b -> f a
  x <* y = (| const x y |)

  when : Bool -> f Unit -> f Unit
  when b x = if b then x else pure tt

  unless : Bool -> f Unit -> f Unit
  unless b = when (not b)

  replicateA! : Nat -> f a -> f Unit
  replicateA! 0 _ = pure tt
  replicateA! (suc n) x = x *> replicateA! n x

  forever : f a -> f b
  forever x = x *> forever x

open Applicative {{...}} public

instance
  Applicative-Function : Applicative (Function a)
  Applicative-Function .pure = const
  Applicative-Function ._<*>_ f g x = f x (g x)

  Applicative-Identity : Applicative Identity
  Applicative-Identity .pure = asIdentity
  Applicative-Identity ._<*>_ f = asIdentity <<< runIdentity f <<< runIdentity

  Applicative-Const : {{Monoid a}} -> Applicative (Const a)
  Applicative-Const .pure _ = asConst mempty
  Applicative-Const ._<*>_ f x = asConst (getConst f <> getConst x)

  Applicative-Maybe : Applicative Maybe
  Applicative-Maybe .pure = just
  Applicative-Maybe ._<*>_ (just f) = map f
  Applicative-Maybe ._<*>_ nothing _ = nothing

  Applicative-List : Applicative List
  Applicative-List .pure = _:: []
  Applicative-List ._<*>_ [] _ = []
  Applicative-List ._<*>_ (f :: fs) xs  = (f <$> xs) <> (fs <*> xs)

  Applicative-Either : Applicative (Either a)
  Applicative-Either .pure = right
  Applicative-Either ._<*>_ (left x) _ = left x
  Applicative-Either ._<*>_ (right f) = map f

  Applicative-Tuple : {{Monoid a}} -> Applicative (Tuple a)
  Applicative-Tuple .pure = (mempty ,_)
  Applicative-Tuple ._<*>_ (u , f) (v , x) = (u <> v , f x)
