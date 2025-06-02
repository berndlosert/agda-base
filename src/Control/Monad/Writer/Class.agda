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
    a b : Type

-------------------------------------------------------------------------------
-- MonadWriter
-------------------------------------------------------------------------------

record MonadWriter (w : Type) (m : Type -> Type) : Type where
  field
    overlap {{Monoid-w}} : Monoid w
    overlap {{Monad-m}} : Monad m
    tell : w -> m Unit

  writer : Tuple w a -> m a
  writer (w , x) = tell w *> pure x

open MonadWriter {{...}} public
