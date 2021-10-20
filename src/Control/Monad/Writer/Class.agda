module Control.Monad.Writer.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- MonadWriter
-------------------------------------------------------------------------------

record MonadWriter (w : Set) (m : Set -> Set) : Set where
  field
    overlap {{Monoid-w}} : Monoid w
    overlap {{Monad-m}} : Monad m
    tell : w -> m Unit
    listen : m a -> m (Pair w a)
    pass : m (Pair (w -> w) a) -> m a

  writer : Pair w a -> m a
  writer (w , x) = do
    tell w
    pure x

  listens : (w -> b) -> m a -> m (Pair a b)
  listens f m = do
    (w , x) <- listen m
    pure (x , f w)

  censor : (w -> w) -> m a -> m a
  censor f m = pass (map (f ,_) m)

open MonadWriter {{...}} public
