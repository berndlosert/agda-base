{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Classes where

open import Prelude

private
  variable
    A B : Set
    M : Set -> Set

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    lift : {{_ : Monad M}} -> M ~> T M
    transform : Monad M -> Monad (T M)

open MonadTrans {{...}} public

record MonadCont (M : Set -> Set) : Set where
  field
    {{Monad:MonadCont}} : Monad M
    callCC : ((A -> M B) -> M A) -> M A

open MonadCont {{...}} public
