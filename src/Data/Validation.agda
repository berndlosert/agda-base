module Data.Validation where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Selective
open import Data.Bifunctor
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e : Set

-------------------------------------------------------------------------------
-- Validation
-------------------------------------------------------------------------------

data Validation (e a : Set) : Set where
  failure : e -> Validation e a
  success : a -> Validation e a

instance
  Functor-Validation : Functor (Validation e)
  Functor-Validation .map f = \ where
    (failure e) -> failure e
    (success x) -> success (f x)

  Applicative-Validation : {{Semigroup e}} -> Applicative (Validation e)
  Applicative-Validation ._<*>_ = \ where
    (failure e1) (failure e2) -> failure (e1 <> e2)
    (failure e) (success _) -> failure e
    (success f) x -> map f x
  Applicative-Validation .pure = success

  Alternative-Validation : {{Monoid e}} -> Alternative (Validation e)
  Alternative-Validation ._<|>_ = \ where
    (failure e1) (failure e2) -> failure (e1 <> e2)
    (success x) _ -> success x
    _ (success x) -> success x
  Alternative-Validation .azero = failure mempty

  Selective-Validation : {{Semigroup e}} -> Selective (Validation e)
  Selective-Validation .select = \ where
    (failure e) _ -> failure e
    (success (left x)) f -> (_$ x) <$> f
    (success (right x)) _ -> success x

  Foldable-Validation : Foldable (Validation e)
  Foldable-Validation .foldr f z = \ where
    (failure _) -> z
    (success x) -> f x z

  Traversable-Validation : Traversable (Validation e)
  Traversable-Validation .traverse f = \ where
    (failure e) -> pure (failure e)
    (success x) -> success <$> f x

  Semigroup-Validation : {{Semigroup e}} -> {{Semigroup a}} -> Semigroup (Validation e a)
  Semigroup-Validation ._<>_ x y = (| x <> y |)

  Monoid-Validation : {{Semigroup e}} -> {{Monoid a}} -> Monoid (Validation e a)
  Monoid-Validation .mempty = success mempty

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

isFailure : Validation e a -> Bool
isFailure (failure _) = true
isFailure _ = false

isSuccess : Validation e a -> Bool
isSuccess (success _) = true
isSuccess _ = false

validation : (e -> b) -> (a -> b) -> Validation e a -> b
validation f g = \ where
  (failure e) -> f e
  (success x) -> g x

failures : List (Validation e a) -> List e
failures [] = []
failures (failure e :: vs) = e :: failures vs
failures (success _ :: vs) = failures vs

successes : List (Validation e a) -> List a
successes [] = []
successes (failure _ :: vs) = successes vs
successes (success x :: vs) = x :: successes vs

partitionValidations : List (Validation e a) -> Pair (List e) (List a)
partitionValidations [] = ([] , [])
partitionValidations (failure e :: vs) = lmap (e ::_) $ partitionValidations vs
partitionValidations (success x :: vs) = map (x ::_) $ partitionValidations vs

fromFailure : e -> Validation e a -> e
fromFailure _ (failure e) = e
fromFailure e _  = e

fromSuccess : a -> Validation e a -> a
fromSuccess _ (success x) = x
fromSuccess x _ = x