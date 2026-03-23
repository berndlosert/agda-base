module Control.Monad.Trans.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad
  using (Monad)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type
    m : Type -> Type

-------------------------------------------------------------------------------
-- MonadTrans
-------------------------------------------------------------------------------

record MonadTrans (t : (Type -> Type) -> Type -> Type) : Type where
  field
    overlap {{Monad-tm}} : {{Monad m}} -> Monad (t m)
    lift : {{Monad m}} -> m a -> t m a

open MonadTrans {{...}} public
