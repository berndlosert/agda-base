{-# OPTIONS --type-in-type #-}

module Data.Bool where

open import Agda.Builtin.Bool public
open import Data.Boolean public
open import Data.Type.Equality

private variable A : Set

infixr 10 if_then_else_
if_then_else_ : Bool -> A -> A -> A
if true then a else _ = a
if false then _ else a = a

IsTrue : Bool -> Set
IsTrue b = b === true

instance
  booleanBool : Boolean Bool
  booleanBool .ff = false
  booleanBool .tt = true
  booleanBool .not = \ where
    true -> false
    false -> true
  booleanBool ._&&_ = \ where
    true true -> true
    _ _ -> false
  booleanBool ._||_ = \ where
    false false -> false
    _ _ -> true
