{-# OPTIONS --type-in-type #-}

module Data.List.Base where

-- List X is the type of finite lists of values of type X. It has two
-- constructors: the empty list [] and the cons operator _::_.

open import Agda.Builtin.List public
  renaming (_∷_ to _::_)

-- Use _++_ for appending lists.

open import Notation.Append public

instance
  Append:List : forall {X} -> Append (List X) (List X) (List X)
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
  Foldable:List .lift = [_]
  Foldable:List .foldMap f [] = mempty
  Foldable:List .foldMap f (x :: xs) = f x <> foldMap f xs

-- List is a monad.

open import Control.Category
open import Control.Monad public

instance
  Monad:List : Monad Sets List
  Monad:List .return = [_]
  Monad:List .extend k [] = []
  Monad:List .extend k (x :: xs) = k x ++ extend k xs

-- List is a functor.

open import Data.Functor public

instance
  Functor:List : Endofunctor Sets List
  Functor:List = Functor: liftM

-- List forms an applicative functor in two ways. The most common way given
-- as an instance below. The other way is from the monad instance.

open import Control.Applicative public

instance
  Applicative:List : Applicative List
  Applicative:List .zip ([] , _) = []
  Applicative:List .zip (_ , []) = []
  Applicative:List .zip (x :: xs , y :: ys) = (x , y) :: zip (xs , ys)
  Applicative:List .unit = [_]

-- List is traversable.

open import Data.Traversable public

instance
  Traversable:List : Traversable List
  Traversable:List .sequence {F} {X} = foldr cons (pure [])
    where
      cons : F X -> F (List X) -> F (List X)
      cons x xs = (| _::_ x xs |)

-- Allows use of _!!_ for indexing into a list.

open import Data.Maybe
open import Data.Nat.Base
open import Notation.Index public

instance
  Index:List : Index List
  Index:List = Index: Nat Maybe index
    where
      index : forall {X} -> List X -> Nat -> Maybe X
      index [] _ = nothing
      index (x :: xs) zero = just x
      index (x :: xs) (suc n) = index xs n
