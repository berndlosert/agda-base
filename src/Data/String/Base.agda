{-# OPTIONS --type-in-type #-}

module Data.String.Base where

import Agda.Builtin.String as Builtin
open import Agda.Builtin.FromString public
open import Data.Eq public
open import Notation.Append public
open import Data.Unit public

-- String is just Text from Haskell.
open Builtin using (String) public

-- This is how we compare strings for equality.
instance
  Eq:String : Eq String
  Eq:String = Eq: Builtin.primStringEquality

-- Use ++ to append strings.
instance
  Append:String : Append String String String
  Append:String = Append: Builtin.primStringAppend

-- We need to define an IsString String instance if we're going to use
-- IsString.
instance
  IsString:String : IsString String
  IsString:String = record {
      Constraint = \ _ -> Unit;
      fromString = \ s -> s
    }
