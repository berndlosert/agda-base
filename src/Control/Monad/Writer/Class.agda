module Control.Monad.Writer.Class where

open import Prelude

private variable a b : Set

record MonadWriter (w : Set) (m : Set -> Set) : Set where
  field
    overlap {{monoid}} : Monoid w
    overlap {{monad}} : Monad m
    tell : w -> m Unit
    listen : m a -> m (a * w)
    pass : m (a * (w -> w)) -> m a

  writer : a * w -> m a
  writer (a , w) = do
    tell w
    return a

  listens : (w -> b) -> m a -> m (a * b)
  listens f m = do
    (a , w) <- listen m
    return (a , f w)

  censor : (w -> w) -> m ~> m
  censor f m = pass do
    a <- m
    return (a , f)

open MonadWriter {{...}} public
