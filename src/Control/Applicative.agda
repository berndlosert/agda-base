{-# OPTIONS --type-in-type #-}

module Control.Applicative where

-- Applicative functors are lax monoidal functors of type Set -> Set that
-- preserve the Cartesian monoidal structure. In other words, a functor
-- F : Set -> Set is applicative when F X * F Y -> F (X * Y) and
-- Unit -> F Unit.

open import Control.Category
open import Data.Function
open import Data.Functor
open import Data.Product
open import Data.Unit

record Applicative (F : Set -> Set) : Set where
  constructor Applicative:
  field
    {{instance:Functor}} : Endofunctor Sets F
    zip : {X Y : Set} -> F X * F Y -> F (X * Y)
    unit : Unit -> F Unit

  private variable X Y Z : Set

  -- The inverse of zip, proving that F X * F Y ~= F (X * Y).
  unzip : F (X * Y) -> F X * F Y
  unzip = pair (map fst) (map snd)

  -- Defining _<*>_ and pure allows use to use idiom brackets (| |) when
  -- writing applicative code.
  infixl 24 _<*>_
  _<*>_ : F (X -> Y) -> F X -> F Y
  f <*> x = map apply (zip (f , x))

  pure : X -> F X
  pure x = map (const x) (unit tt)

  -- For applicative functors, the mapping function map (called liftA) can be
  -- generalized to any number of arguments.
  liftA : (X -> Y) -> F X -> F Y
  liftA = map

  -- This is the two-argument version.
  liftA2 : (X -> Y -> Z) -> F X -> F Y -> F Z
  liftA2 f x = map f x <*>_

  -- Generalization of flip const.
  infixl 24 _*>_
  _*>_ : F X -> F Y -> F Y
  _*>_ = liftA2 (flip const)

  -- Generalization of const.
  infixl 24 _<*_
  _<*_ : F X -> F Y -> F X
  _<*_ = liftA2 const

open Applicative {{...}} public

-- A convenient constructor of applicative instances that defines unit and
-- zip in terms of pure and <*>.
Idiom: : {F : Set -> Set} {{_ : Endofunctor Sets F}}
 -> ({X Y : Set} -> F (X -> Y) -> F X -> F Y)
 -> ({X : Set} -> X -> F X)
 -> Applicative F
Idiom: _<*>_ pure = record {
    zip = \ { (x , y) -> (pure _,_ <*> x) <*> y };
    unit = pure {Unit}
  }

-- Every monad of type Set -> Set is an applicative with unit = return
-- and _<*>_ = ap, where ap defined as follows:
open import Control.Monad
ap : {F : Set -> Set} {{_ : Monad Sets F}} {X Y : Set}
  -> F (X -> Y) -> F X -> F Y
ap fs xs = do
  f <- fs
  x <- xs
  return (f x)
