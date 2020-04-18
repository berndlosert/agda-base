{-# OPTIONS --type-in-type #-}

module Data.Either where

open import Control.Applicative
open import Control.Monad
open import Data.Bool
open import Data.Functor
open import Data.Eq
open import Data.Foldable
open import Data.Function
open import Data.Monoid
open import Data.Semigroup
open import Data.Traversable
open import Prim

private variable A B C D : Set

either : (A -> C) -> (B -> C) -> Either A B -> C
either f g (left x) = f x
either f g (right y) = g y

mirror : Either A B -> Either B A
mirror = either right left

untag : Either A A -> A
untag = either id id

isLeft : Either A B -> Bool
isLeft = either (const true) (const false)

isRight : Either A B -> Bool
isRight = not <<< isLeft

fromLeft : A -> Either A B -> A
fromLeft x = either id (const x)

fromRight : B -> Either A B -> B
fromRight y = either (const y) id

fromEither : (A -> B) -> Either A B -> B
fromEither f = either f id

instance
  eqEither : {{_ : Eq A}} {{_ : Eq B}} -> Eq (Either A B)
  eqEither ._==_ = \ where
    (left x) (left y) -> x == y
    (right x) (right y) -> x == y
    _ _ -> false

  functorEither : Functor (Either A)
  functorEither .map f = \ where
    (left a) -> left a
    (right x) -> right (f x)

  bifunctorEither : Bifunctor Either
  bifunctorEither .bimap f g = either (left <<< f) (right <<< g)

  applicativeEither : Applicative (Either A)
  applicativeEither .pure = right
  applicativeEither ._<*>_ = \ where
    (left a) _ -> left a
    (right f) r -> map f r

  monadEither : Monad (Either A)
  monadEither ._>>=_ = \ where
    (left a) k -> left a
    (right x) k -> k x

  foldableEither : Foldable (Either A)
  foldableEither .foldMap _ (left _) = mempty
  foldableEither .foldMap f (right y) = f y

  traversableEither : Traversable (Either A)
  traversableEither .traverse f = \ where
    (left x) -> pure (left x)
    (right y) -> right <$> f y

  semigroupSumSet : Semigroup (Sum Set)
  semigroupSumSet ._<>_ A B = toSum $ Either (fromSum A) (fromSum B)

  monoidSumSet : Monoid (Sum Set)
  monoidSumSet .mempty = toSum Void
