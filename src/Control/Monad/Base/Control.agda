module Control.Monad.Base.Control where

open import Prelude

private variable a : Set

record MonadBaseControl (b m : Set -> Set) : Set where
  field
    StM : Set -> Set
    liftBaseWith : ((forall {a} -> m a -> b (StM a)) -> b a) -> m a
    restoreM : StM ~> m

open MonadBaseControl {{...}}

instance
  monadBaseControlMaybe : MonadBaseControl Maybe Maybe
  monadBaseControlMaybe .StM = id
  monadBaseControlMaybe .liftBaseWith f = f id
  monadBaseControlMaybe .restoreM = return
