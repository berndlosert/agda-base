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
    a : Set

-------------------------------------------------------------------------------
-- Iter
-------------------------------------------------------------------------------

Iter : Set -> Set
Iter = IterT Identity

execIter : Iter a -> a
execIter = runIdentity <<< execIterT

execIter' : Nat -> Iter a -> Maybe a
execIter' n = runIdentity <<< execIterT' n
