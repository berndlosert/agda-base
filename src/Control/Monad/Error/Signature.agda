module Control.Monad.Error.Signature where

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
-- AnError
-------------------------------------------------------------------------------

data Throwing (e k : Type) : Type where
  Throw : e -> k -> Throwing e k