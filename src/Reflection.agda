{-# OPTIONS --type-in-type #-}

module Reflection where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Reflection

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Agda.Builtin.Reflection public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Eq-Name : Eq Name
  Eq-Name ._==_ = primQNameEquality

  Ord-Name : Ord Name
  Ord-Name .compare m n =
    if m == n
      then EQ
      else
        if primQNameLess m n
          then LT
          else GT

  Show-Name : Show Name
  Show-Name .showsPrec d n = showString (primShowQName n)

  Functor-TC : Functor TC
  Functor-TC .map f m = bindTC m (f >>> returnTC)

  Applicative-TC : Applicative TC
  Applicative-TC .pure = returnTC
  Applicative-TC ._<*>_ m k =
    bindTC m \ f -> bindTC k \ x -> pure (f x)

  Monad-TC : Monad TC
  Monad-TC ._>>=_ = bindTC


