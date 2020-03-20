{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Class where

open import Prelude

private variable M : Set -> Set

-- A monad transformer is an pointed endofunctor in the category of monads.
record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    lift : {{_ : Monad M}} -> M ~> T M
    transform : {{_ : Monad M}} -> Monad (T M)

open MonadTrans {{...}} public
