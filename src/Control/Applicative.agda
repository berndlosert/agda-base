{-# OPTIONS --type-in-type #-}

module Control.Applicative where

-- A functor F : Set -> Set is applicative when:
--  * forall {X Y} -> F X * F Y -> F (X * Y) and
--  * Unit -> F Unit.

open import Control.Category
open import Data.Function
open import Data.Functor
open import Data.Tuple public
open import Data.Unit
open import Notation.Mul

record Applicative (F : Set -> Set) : Set where
  constructor Applicative:
  field
    overlap {{Functor:Applicative}} : Endofunctor Sets F
    zip : forall {X Y} -> F X * F Y -> F (X * Y)
    unit : Unit -> F Unit

  -- The inverse of zip, proving that F X * F Y ~= F (X * Y).

  unzip : forall {X Y} -> F (X * Y) -> F X * F Y
  unzip = pair (map fst) (map snd)

  -- Defining _<*>_ and pure allows use to use idiom brackets (|_|) when
  -- writing applicative code.

  infixl 24 _<*>_

  _<*>_ : forall {X Y} -> F (X -> Y) -> F X -> F Y
  f <*> x = apply <$> zip (f , x)

  -- Lift a value.

  pure : forall {X} -> X -> F X
  pure x = const x <$> unit tt

  -- This is the two-argument version of map.

  map2 : forall {X Y Z} -> (X -> Y -> Z) -> F X -> F Y -> F Z
  map2 f x y = f <$> x <*> y

  -- This is the three-argument version of map.

  map3 : forall {W X Y Z} -> (W -> X -> Y -> Z) -> F W -> F X -> F Y -> F Z
  map3 f w x y = f <$> w <*> x <*> y

  -- Generalization of flip const.

  infixl 24 _*>_

  _*>_ : forall {X Y} -> F X -> F Y -> F Y
  x *> y = flip const <$> x <*> y

  -- Generalization of const.

  infixl 24 _<*_

  _<*_ : forall {X Y} -> F X -> F Y -> F X
  x <* y = const <$> x <*> y

open Applicative {{...}} public

-- A convenient constructor of applicative instances that defines unit and
-- zip in terms of pure and _<*>_.

Idiom: : forall {F} {{_ : Endofunctor Sets F}}
  -> (forall {X Y} -> F (X -> Y) -> F X -> F Y)
  -> (forall {X} -> X -> F X)
  -> Applicative F
Idiom: _<*>_ pure .zip (x , y) = (pure _,_ <*> x) <*> y
Idiom: _<*>_ pure .unit = pure {Unit}

-- Every monad of type Set -> Set is an applicative with unit = return
-- and _<*>_ = ap, where ap defined as follows:

open import Control.Monad

ap : forall {F X Y} {{_ : Monad Sets F}}
  -> F (X -> Y) -> F X -> F Y
ap fs xs = do
  f <- fs
  x <- xs
  return (f x)
