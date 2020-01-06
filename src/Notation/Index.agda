{-# OPTIONS --type-in-type #-}

module Notation.Index where

-- Index operator.

record Index (Container : Set -> Set) : Set where
  constructor Index:
  field
    Position : Set
    Result : Set -> Set
    _!!_ : forall {X} -> Container X -> Position -> Result X
  infixl 9 _!!_

open Index {{...}} public
  hiding (Position; Result)
