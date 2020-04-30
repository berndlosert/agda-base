{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont.Class where

open import Prelude

private variable A B : Set

record MonadCont (M : Set -> Set) : Set where
  field
    {{monad}} : Monad M
    callCC : ((A -> M B) -> M A) -> M A

open MonadCont {{...}} public
