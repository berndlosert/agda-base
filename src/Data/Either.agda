{-# OPTIONS --type-in-type #-}

module Data.Either where

open import Control.Monad
open import Data.Bool
open import Data.Eq
open import Data.Function

private variable A B C D : Set

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

{-# COMPILE GHC Either = data Either (Left | Right) #-}

either : (A -> C) -> (B -> C) -> Either A B -> C
either f g (left x) = f x
either f g (right y) = g y

plus : (A -> B) -> (C -> D) -> Either A C -> Either B D
plus f g = either (left <<< f) (right <<< g)

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

  applicativeEither : Applicative (Either A)
  applicativeEither .pure = right
  applicativeEither ._<*>_ = \ where
    (left a) _ -> left a
    (right f) r -> map f r

  monadEither : Monad (Either A)
  monadEither ._>>=_ = \ where
    (left a) k -> left a
    (right x) k -> k x
