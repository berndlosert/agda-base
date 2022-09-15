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

  Functor-TC : Functor TC
  Applicative-TC : Applicative TC
  Monad-TC : Monad TC

  Functor-TC .map = liftM
  Applicative-TC ._<*>_ = ap
  Applicative-TC .pure = returnTC
  Monad-TC ._>>=_ = bindTC
