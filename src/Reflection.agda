module Reflection where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Reflection
open import Control.Monad.Kleisli

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

  Triple-TC : Triple TC
  Triple-TC .flatMap = flip bindTC
  Triple-TC .return = returnTC

  Functor-TC : Functor TC
  Functor-TC .map = liftM

  Applicative-TC : Applicative TC
  Applicative-TC .pure = return
  Applicative-TC ._<*>_ = ap

  Monad-TC : Monad TC
  Monad-TC ._>>=_ = bind
