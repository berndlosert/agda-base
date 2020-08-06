module Control.Monad.Base where

open import Prelude

private variable a : Set

record MonadBase (b m : Set -> Set) : Set where
  field liftBase : b ~> m

open MonadBase {{...}} public
