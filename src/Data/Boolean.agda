{-# OPTIONS --type-in-type #-}

module Data.Boolean where

open import Data.Function

private variable A B : Set

record Boolean (B : Set) : Set where
  infixr 2 _||_
  infixr 3 _&&_
  field
    ff : B
    tt : B
    not : B -> B
    _&&_ : B -> B -> B
    _||_ : B -> B -> B

open Boolean {{...}} public

instance
  booleanFunction : {{_ : Boolean B}} -> Boolean (A -> B)
  booleanFunction .ff = const ff
  booleanFunction .tt = const tt
  booleanFunction .not f = not <<< f
  booleanFunction ._&&_ f g a = f a && g a
  booleanFunction ._||_ f g a = f a || g a
