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
  Ord-Name ._<_ = primQNameLess

  Show-Name : Show Name
  Show-Name .showsPrec d n = showString (primShowQName n)

  Monad-TC : Monad TC
  Monad-TC = asMonad bindTC returnTC

  Applicative-TC : Applicative TC
  Applicative-TC = Monad-TC .Applicative-super

  Functor-TC : Functor TC
  Functor-TC = Applicative-TC .Functor-super
