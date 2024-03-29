module Control.Monad.Reader.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- MonadReader
-------------------------------------------------------------------------------
record MonadReader (r : Type) (m : Type -> Type) : Type where
  field
    overlap {{Monad-m}} : Monad m
    ask : m r

  asks : (r -> a) -> m a
  asks f = (| f ask |)

open MonadReader {{...}} public
