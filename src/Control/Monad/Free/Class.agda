module Control.Monad.Free.Class where

open import Prelude

record MonadFree (f m : Set -> Set) : Set where
  field wrap : f <<< m ~> m

open MonadFree {{...}} public
