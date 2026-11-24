module Data.Functor where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Control.Semigroupoid using (_<<<_)
open import Data.Functor.Const using (Const; asConst; getConst)
open import Data.Functor.Identity using (Identity; asIdentity; runIdentity)
open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Functor
-------------------------------------------------------------------------------

record Functor (f : Type -> Type) : Type where
  field map : (a -> b) -> f a -> f b

  infixl 4 _<$>_
  _<$>_ : (a -> b) -> f a -> f b
  _<$>_ = map

  infixl 1 _<&>_
  _<&>_ : f a -> (a -> b) -> f b
  _<&>_ = flip map

  infixl 4 _<$_
  _<$_ : b -> f a -> f b
  _<$_ = map <<< const

  infixl 4 _$>_
  _$>_ : f a -> b -> f b
  _$>_ = flip _<$_

open Functor {{...}} public

instance
  Functor-Function : Functor (Function a)
  Functor-Function .map = _<<<_

  Functor-Identity : Functor Identity
  Functor-Identity .map f = asIdentity <<< f <<< runIdentity

  Functor-Const : Functor (Const a)
  Functor-Const .map _ = asConst <<< getConst

  Functor-Maybe : Functor Maybe
  Functor-Maybe .map f = maybe nothing (just <<< f)

  Functor-List : Functor List
  Functor-List .map f [] = []
  Functor-List .map f (x :: xs) = f x :: map f xs

  Functor-Either : Functor (Either a)
  Functor-Either .map f = either left (right <<< f)

  Functor-Tuple : Functor (Tuple a)
  Functor-Tuple .map f (x , y) = (x , f y)
