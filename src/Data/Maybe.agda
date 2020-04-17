{-# OPTIONS --type-in-type #-}

module Data.Maybe where

open import Control.Alternative
open import Control.Applicative
open import Control.Monad
open import Data.Bool
open import Data.Foldable
open import Data.Function
open import Data.Functor
open import Data.Either
open import Data.Eq
open import Data.Monoid
open import Data.Semigroup
open import Data.Traversable
open import Prim

private variable A B : Set

isJust : Maybe A -> Bool
isJust (just _) = true
isJust _ = false

isNothing : Maybe A -> Bool
isNothing = not <<< isJust

maybe : B -> (A -> B) -> Maybe A -> B
maybe b f nothing = b
maybe b f (just a) = f a

fromMaybe : A -> Maybe A -> A
fromMaybe = flip maybe id

maybeToLeft : B -> Maybe A -> Either A B
maybeToLeft b = maybe (right b) left

maybeToRight : B -> Maybe A -> Either B A
maybeToRight b = mirror <<< maybeToLeft b

leftToMaybe : Either A B -> Maybe A
leftToMaybe = either just (const nothing)

rightToMaybe : Either A B -> Maybe B
rightToMaybe = leftToMaybe <<< mirror

ensure : (A -> Bool) -> A -> Maybe A
ensure p a = if p a then just a else nothing

instance
  eqMaybe : {{_ : Eq A}} -> Eq (Maybe A)
  eqMaybe ._==_ = \ where
    nothing nothing -> true
    (just x) (just y) -> x == y
    _ _ -> false

  functorMaybe : Functor Maybe
  functorMaybe .map f = \ where
    nothing -> nothing
    (just a) -> just (f a)

  applicativeMaybe : Applicative Maybe
  applicativeMaybe .pure = just
  applicativeMaybe ._<*>_ = \ where
    (just f) m -> map f m
    nothing _ -> nothing

  alternativeMaybe : Alternative Maybe
  alternativeMaybe .empty = nothing
  alternativeMaybe ._<|>_ = \ where
    nothing r -> r
    l _ -> l

  monadMaybe : Monad Maybe
  monadMaybe ._>>=_ = \ where
    nothing k -> nothing
    (just x) k -> k x

  foldableMaybe : Foldable Maybe
  foldableMaybe .foldMap = maybe mempty

  traversableMaybe : Traversable Maybe
  traversableMaybe .traverse f = \ where
    nothing -> pure nothing
    (just x) -> just <$> f x

  semigroupMaybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  semigroupMaybe ._<>_ = \ where
    nothing m -> m
    m nothing -> m
    (just x) (just y) -> just (x <> y)

  monoidMaybe : {{_ : Semigroup A}} -> Monoid (Maybe A)
  monoidMaybe .mempty = nothing
