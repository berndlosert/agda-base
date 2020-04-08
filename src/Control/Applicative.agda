{-# OPTIONS --type-in-type #-}

module Control.Applicative where

open import Data.Function
open import Data.Functor public

private variable A B C : Set

record Applicative (F : Set -> Set) : Set where
  infixl 4 _<*>_
  field
    overlap {{super}} : Functor F
    _<*>_ : F (A -> B) -> F A -> F B
    pure : A -> F A

  infixl 4 _*>_
  _*>_ : F A -> F B -> F B
  a *> b = (| (flip const) a b |)

  infixl 4 _<*_
  _<*_ : F A -> F B -> F A
  a <* b = (| const a b |)

  map2 : (A -> B -> C) -> F A -> F B -> F C
  map2 f x y = (| f x y |)

open Applicative {{...}} public
