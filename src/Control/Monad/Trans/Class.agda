{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Class where

open import Prelude

private
  variable
    a : Set
    m : Set -> Set

-- A monad transformer is an pointed invariant endofunctor in the category
-- of monads.
record MonadTrans (t : (Set -> Set) -> Set -> Set) : Set where
  field
    overlap {{transform}} : {{_ : Monad m}} -> Monad (t m)
    lift : {{_ : Monad m}} -> m a -> t m a

open MonadTrans {{...}} public
