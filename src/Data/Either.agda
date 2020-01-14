{-# OPTIONS --type-in-type #-}

module Data.Either where

-- Either is used to form coproducts (disjoint unions) in the category Sets.

data Either (X Y : Set) : Set where
  left : X -> Either X Y
  right : Y -> Either X Y

-- This instance makes it possible to write X + Y for Either X Y.

open import Notation.Add public

instance
  Add:Set : Add Set
  Add:Set = Add: Either

-- The function either is evidence that Either satisfies the universal property
-- of coproducts in the category Sets. You can also think of it as the fold
-- operation for Either.

either : {X Y Z : Set} -> (X -> Z) -> (Y -> Z) -> X + Y -> Z
either f g (left x) = f x
either f g (right y) = g y

-- Shorthand for either id id.

untag : forall {X} -> X + X -> X
untag (left x) = x
untag (right x) = x

-- X + Y and Y + X are isomorphic and the isomorphism is called mirror.

mirror : forall {X Y} -> X + Y -> Y + X
mirror (left x) = right x
mirror (right y) = left y

-- The injections left and right have two pseudoduals called leftToMaybe and
-- rightToMaybe.

open import Data.Maybe.Base

leftToMaybe : forall {X Y} -> X + Y -> Maybe X
leftToMaybe (left x) = just x
leftToMaybe _ = nothing

rightToMaybe : forall {X Y} -> X + Y -> Maybe Y
rightToMaybe (right y) = just y
rightToMaybe _ = nothing

-- _+_ forms a bifunctor in the obvious way. The map operation of this
-- bifunctor in uncurried form is plus:

plus : forall {X X' Y Y'} -> (X -> Y) -> (X' -> Y') -> X + X' -> Y + Y'
plus f g (left x) = left (f x)
plus f g (right y) = right (g y)
