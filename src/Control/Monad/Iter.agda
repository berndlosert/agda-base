{-# OPTIONS --type-in-type #-}

module Control.Monad.Iter where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Iter.Trans

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Iter
-------------------------------------------------------------------------------

Iter : Set -> Size -> Set
Iter a i = IterT Identity a i

{-# TERMINATING #-}
unsafeRunIter : Iter a Inf -> a
unsafeRunIter iter = runIdentity (unsafeRunIterT iter)
