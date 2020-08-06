module Control.Monad.Base where

open import Prelude

record MonadBase (b n : Set -> Set) : Set where
  field liftBase : b ~> n

open MonadBase {{...}} public
