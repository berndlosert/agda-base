module Reflection where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Agda.Builtin.Reflection
open import Control.Applicative using (Applicative; _<*>_; pure)
open import Control.Monad using (Monad; _>>=_; liftM; ap)
open import Data.Functor using (Functor; map)
open import Data.Show
open import Prelude

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
  Show-Name .show = primShowQName
  Show-Name .showsPrec = showsPrecDefault

  mutual
    Functor-TC : Functor TC
    Functor-TC .map = liftM

    Applicative-TC : Applicative TC
    Applicative-TC ._<*>_ = ap
    Applicative-TC .pure = returnTC

    Monad-TC : Monad TC
    Monad-TC ._>>=_ = bindTC
