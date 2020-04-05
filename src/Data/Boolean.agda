{-# OPTIONS --type-in-type #-}

module Data.Boolean where

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
