{-# OPTIONS --type-in-type #-}

module Reflection where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Reflection
open import Data.Dictionary

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Agda.Builtin.Reflection public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

private
  MonadDict-TC : Dict Monad TC
  MonadDict-TC .bind = bindTC
  MonadDict-TC .return = returnTC

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

  Monad-TC : Monad TC
  Monad-TC = fromDict MonadDict-TC

  Applicative-TC : Applicative TC
  Applicative-TC = Monad-TC .Applicative-super

  Functor-TC : Functor TC
  Functor-TC = Applicative-TC .Functor-super
