{-# OPTIONS --type-in-type #-}

module Control.Monad.Iter where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Iter.Trans

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Iter.Trans public
  using (
    Now; Later;
    delay; never;
    Functor-IterT; Applicative-IterT; Monad-IterT; Alternative-IterT
  )

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Iter
-------------------------------------------------------------------------------

Iter : Size -> Set -> Set
Iter i a = IterT i Identity a

{-# TERMINATING #-}
unsafeIter : Iter Inf a -> a
unsafeIter iter = runIdentity (unsafeIterT iter)
