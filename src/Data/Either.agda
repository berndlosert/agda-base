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

-- Left and right projections.

open import Data.Maybe.Base

fromLeft : forall {X Y} -> X + Y -> Maybe X
fromLeft (left x) = just x
fromLeft _ = nothing

fromRight : forall {X Y} -> X + Y -> Maybe Y
fromRight (right y) = just y
fromRight _ = nothing

-- Turn a Maybe into an Either.

note : forall {X Y} -> X -> Maybe Y -> Either X Y
note x nothing = left x
note x (just y) = right y

-- _+_ forms a bifunctor in the obvious way. The map operation of this
-- bifunctor in uncurried form is plus:

plus : forall {X X' Y Y'} -> (X -> Y) -> (X' -> Y') -> X + X' -> Y + Y'
plus f g (left x) = left (f x)
plus f g (right y) = right (g y)

-- Either X is a monad/applicative/functor for every X.

open import Control.Monad

instance
  Monad:Either : forall {X} -> Monad Sets (Either X)
  Monad:Either .return y = right y
  Monad:Either .extend f (right y) = f y
  Monad:Either .extend f (left x) = left x

  Functor:Either : forall {X} -> Endofunctor Sets (Either X)
  Functor:Either .map = liftM

  Applicative:Either : forall {X} -> Applicative (Either X)
  Applicative:Either = Idiom: ap return
