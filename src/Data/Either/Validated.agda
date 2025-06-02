module Data.Either.Validated where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Lens
open import Control.Selective
open import Data.Bifunctor
open import Data.Filterable
open import Data.Monoid.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e : Type

-------------------------------------------------------------------------------
-- Validated
-------------------------------------------------------------------------------

record Validated (e a : Type) : Type where
  constructor eitherToValidated
  field validatedToEither : Either e a

open Validated public

pattern invalid e = eitherToValidated (left e)
pattern valid x = eitherToValidated (right x)

instance
  Wrapped-Validated : Wrapped (Validated e a) (Either e a)
  Wrapped-Validated .wrapped = iso validatedToEither eitherToValidated

  Semigroup-Validated : {{Semigroup e}} -> Semigroup (Validated e a)
  Semigroup-Validated ._<>_ = \ where
    (invalid e1) (invalid e2) -> invalid (e1 <> e2)
    (valid x) _ -> valid x
    _ (valid x) -> valid x

  Monoid-Validated : {{Monoid e}} -> Monoid (Validated e a)
  Monoid-Validated .mempty = invalid mempty

  Functor-Validated : Functor (Validated e)
  Functor-Validated .map f = \ where
    (invalid e) -> invalid e
    (valid x) -> valid (f x)

  Bifunctor-Validated : Bifunctor Validated
  Bifunctor-Validated .lmap f = \ where
    (invalid e) -> invalid (f e)
    (valid x) -> valid x

  Applicative-Validated : {{Semigroup e}} -> Applicative (Validated e)
  Applicative-Validated ._<*>_ = \ where
    (invalid e1) (invalid e2) -> invalid (e1 <> e2)
    (invalid e) (valid _) -> invalid e
    (valid f) x -> map f x
  Applicative-Validated .pure = valid

  Alternative-Validated : {{Monoid e}} -> Alternative (Validated e)
  Alternative-Validated ._<|>_ = _<>_
  Alternative-Validated .azero = mempty

  Selective-Validated : {{Semigroup e}} -> Selective (Validated e)
  Selective-Validated .eitherS l r = \ where
    (invalid e) -> invalid e
    (valid (left x)) -> l <*> (valid x)
    (valid (right x)) -> r <*> (valid x)

  Foldable-Validated : Foldable (Validated e)
  Foldable-Validated .foldMap f = \ where
    (invalid _) -> mempty
    (valid x) -> f x

  Traversable-Validated : Traversable (Validated e)
  Traversable-Validated .traverse f = \ where
    (invalid e) -> pure (invalid e)
    (valid x) -> valid <$> f x

  Filterable-Validated : {{Monoid e}} -> Filterable (Validated e)
  Filterable-Validated .mapMaybe f = \ where
    (invalid e) -> invalid e
    (valid x) -> maybe (invalid mempty) valid (f x)

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

isInvalid : Validated e a -> Bool
isInvalid (invalid _) = true
isInvalid _ = false

isValid : Validated e a -> Bool
isValid (valid _) = true
isValid _ = false

validated : (e -> b) -> (a -> b) -> Validated e a -> b
validated f g = \ where
  (invalid e) -> f e
  (valid x) -> g x

fromInvalid : e -> Validated e a -> e
fromInvalid _ (invalid e) = e
fromInvalid e _  = e

fromValid : a -> Validated e a -> a
fromValid _ (valid x) = x
fromValid x _ = x