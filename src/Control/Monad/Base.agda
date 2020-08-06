module Control.Monad.Base where

open import Prelude

record MonadBase (b m : Set -> Set) : Set where
  field liftBase : b ~> m

open MonadBase {{...}} public
