{-# OPTIONS --type-in-type #-}

module Data.Maybe where

open import Control.Alternative using (Alternative)
open import Control.Alternative public using (_<|>_; empty)
open import Control.Applicative using (Applicative)
open import Control.Applicative public using (_<*>_; pure)
open import Control.Monad using (Monad)
open import Control.Monad public using (_>>=_; return)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Either using (Either; right; left; mirror; either)
open import Data.Eq using (Eq)
open import Data.Eq public using (_==_; _/=_)
open import Data.Function using (_<<<_; flip; id; const)
open import Data.Functor using (Functor)
open import Data.Functor public using (map)
open import Data.Monoid using (Monoid; mempty)
open import Data.Semigroup using (Semigroup; _<>_)

private variable A B : Set

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

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

  semigroupMaybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  semigroupMaybe ._<>_ = \ where
    nothing m -> m
    m nothing -> m
    (just x) (just y) -> just (x <> y)

  monoidMaybe : {{_ : Semigroup A}} -> Monoid (Maybe A)
  monoidMaybe .mempty = nothing
