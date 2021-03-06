{-# OPTIONS --type-in-type --guardedness #-}

module Control.Monad.Iter where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Iter.Trans
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Iter.Trans public
open Data.Functor.Identity public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Iter
-------------------------------------------------------------------------------

Iter : Type -> Type
Iter = IterT Identity

{-# NON_TERMINATING #-}
execIter : Iter a -> a
execIter = runIdentity <<< execIterT
