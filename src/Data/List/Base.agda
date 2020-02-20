{-# OPTIONS --type-in-type #-}

module Data.List.Base where

-- List X is the type of finite lists of values of type X. It has two
-- constructors: the empty list [] and the cons operator _::_.

open import Agda.Builtin.List public
  renaming (_∷_ to _::_)

-- Useful pattern synonyms for building and deconstructing lists.

pattern [_] x1 =
  x1 :: []
pattern [_,_] x1 x2 =
  x1 :: x2 :: []
pattern [_,_,_] x1 x2 x3 =
  x1 :: x2 :: x3 :: []
pattern [_,_,_,_] x1 x2 x3 x4 =
  x1 :: x2 :: x3 :: x4 :: []
pattern [_,_,_,_,_] x1 x2 x3 x4 x5 =
  x1 :: x2 :: x3 :: x4 :: x5 :: []
pattern [_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: []
pattern [_,_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 x7 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: []
pattern [_,_,_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 x7 x8 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: []
pattern [_,_,_,_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 x7 x8 x9 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: []
pattern [_,_,_,_,_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: []

-- Use _++_ for appending lists.

open import Notation.Append public

instance
  Append:List : forall {X} -> Append (List X) (List X) (List X)
  Append:List ._++_ [] ys = ys
  Append:List ._++_ (x :: xs) ys = x :: xs ++ ys

-- List X is a semigroup for any X.

open import Data.Semigroup public

instance
  Semigroup:List : {X : Set} -> Semigroup (List X)
  Semigroup:List = Semigroup: _++_

-- List X is a monoid for any X.

open import Data.Monoid public

instance
  Monoid:List : {X : Set} -> Monoid (List X)
  Monoid:List = Monoid: []

-- List is foldable.

open import Data.Foldable public

instance
  Foldable:List : Foldable List
  Foldable:List .foldMap f [] = mempty
  Foldable:List .foldMap f (x :: xs) = f x <> foldMap f xs

-- List forms a functor.

open import Data.Functor public

instance
  Functor:List : Endofunctor Sets List
  Functor:List .map f [] = []
  Functor:List .map f (x :: xs) = f x :: map f xs

-- List forms a monad.

open import Control.Category
open import Control.Monad public

instance
  Monad:List : Monad Sets List
  Monad:List .return = [_]
  Monad:List .extend k [] = []
  Monad:List .extend k (x :: xs) = k x ++ extend k xs

-- The Applicative instance of List is derived from the Monad instance.

open import Control.Applicative public

instance
  Applicative:List : Applicative List
  Applicative:List = Applicative: ap return

-- List is an an alternative.

instance
  Alternative:List : Alternative List
  Alternative:List ._<|>_ = _++_
  Alternative:List .empty = []

-- List is traversable.

open import Data.Traversable public

instance
  Traversable:List : Traversable List
  Traversable:List .sequence {F} {X} = foldr cons (pure [])
    where
      cons : F X -> F (List X) -> F (List X)
      cons x xs = (| _::_ x xs |)
