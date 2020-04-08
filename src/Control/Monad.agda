{-# OPTIONS --type-in-type #-}

module Control.Monad where

open import Control.Applicative public
open import Data.Function

private variable A B C : Set

record Monad (M : Set -> Set) : Set where
  infixl 1 _>>=_
  field
    overlap {{super}} : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B

  return : A -> M A
  return = pure

  infixr 1 _=<<_
  _=<<_ : (A -> M B) -> M A -> M B
  _=<<_ = flip _>>=_

  join : M (M A) -> M A
  join = _=<<_ id

  infixl 1 _>>_
  _>>_ : M A -> M B -> M B
  _>>_ = _*>_

  infixr 1 _<<_
  _<<_ : M A -> M B -> M A
  _<<_ = _<*_

  infixr 1 _<=<_
  _<=<_ : (B -> M C) -> (A -> M B) -> A -> M C
  g <=< f = f >>> (_>>= g)

  infixr 1 _>=>_
  _>=>_ : (A -> M B) -> (B -> M C) -> A -> M C
  _>=>_ = flip _<=<_

open Monad {{...}} public
