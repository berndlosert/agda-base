{-# OPTIONS --type-in-type #-}

module Control.Monad.Except where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Except.Trans
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Except.Trans public
open Data.Functor.Identity public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e e' : Set

-------------------------------------------------------------------------------
-- Except
-------------------------------------------------------------------------------

Except : Set -> Set -> Set
Except e = ExceptT e Identity

runExcept : Except e a -> e + a
runExcept = runIdentity <<< runExceptT

mapExcept : (e + a -> e' + b) -> Except e a -> Except e' b
mapExcept f = mapExceptT (Identity: <<< f <<< runIdentity)

withExcept : (e -> e') -> Except e a -> Except e' a
withExcept = withExceptT
