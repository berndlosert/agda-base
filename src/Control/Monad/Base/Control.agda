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
  MonadBaseControl-Maybe : MonadBaseControl Maybe Maybe
  MonadBaseControl-Maybe .StM = id
  MonadBaseControl-Maybe .liftBaseWith f = f id
  MonadBaseControl-Maybe .restoreM = return
