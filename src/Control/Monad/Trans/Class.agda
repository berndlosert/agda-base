{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Class where

open import Prelude

private variable M N : Set -> Set

-- A monad transformer is an pointed invariant endofunctor in the category
-- of monads.
record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    {{transform}} : {{_ : Monad M}} -> Monad (T M)
    lift : {{_ : Monad M}} -> M ~> T M
    tmap : {{_ : Monad M}} {{_ : Monad N}}
      -> (M ~> N) -> (N ~> M) -> T M ~> T N

open MonadTrans {{...}} public
