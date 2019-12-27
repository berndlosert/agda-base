{-# OPTIONS --type-in-type #-}

module Data.List.Base where

-- List X is the type of finite lists of values of type X. It has two
-- constructors: the empty list [] and the cons operator _::_.

import Agda.Builtin.List as Builtin

List = Builtin.List
pattern [] = Builtin.[]
pattern _::_ x y = Builtin._∷_ x y
infixr 5 _::_

-- Use _++_ for appending lists.

open import Notation.Append public

instance Append:List : forall {X} -> Append (List X)
Append:List {X} = Append: append
  where
    append : List X -> List X -> List X
    append [] ys = ys
    append (x :: xs) ys = x :: append xs ys

-- Notation for constructing/deconstructing lists. Note that we use # instead
-- of , to separate list items because Agda gets confused when we use , for
-- the separator.

pattern [_] x = x :: []
pattern [_#_] x y = x :: y :: []
pattern [_#_#_] x y z = x :: y :: z :: []
pattern [_#_#_#_] w x y z = w :: x :: y :: z :: []
pattern [_#_#_#_#_] v w x y z = v :: w :: x :: y :: z :: []
pattern [_#_#_#_#_#_] u v w x y z = u :: v :: w :: x :: y :: z :: []

-- List X is a semigroup for any X.

open import Data.Semigroup

instance
  Semigroup:List : {X : Set} -> Semigroup (List X)
  Semigroup:List = Semigroup: _++_

-- List X is a monoid for any X.

open import Data.Monoid

instance
  Monoid:List : {X : Set} -> Monoid (List X)
  Monoid:List = Monoid: []
