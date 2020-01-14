{-# OPTIONS --type-in-type #-}

module Data.String.Base where

-- String is just Text from Haskell.

import Agda.Builtin.String as Builtin

open Builtin using (String) public

-- This is how we compare strings for equality.

open import Data.Eq public

instance
  Eq:String : Eq String
  Eq:String = Eq: Builtin.primStringEquality

-- Use ++ to append strings.

open import Notation.Append public

instance
  Append:String : Append String String String
  Append:String = Append: Builtin.primStringAppend

-- We need to define an IsString String instance if we're going to use
-- IsString.

open import Agda.Builtin.FromString public
open import Data.Unit public

instance
  IsString:String : IsString String
  IsString:String = record {
      Constraint = \ _ -> Unit;
      fromString = \ s -> s
    }

-- String is a semigroup.

open import Data.Semigroup public

instance
  Semigroup:String : Semigroup String
  Semigroup:String = Semigroup: _++_

-- String is a monoid.

open import Data.Monoid public

instance
  Monoid:String : Monoid String
  Monoid:String = Monoid: ""
