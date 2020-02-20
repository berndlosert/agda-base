{-# OPTIONS --type-in-type #-}

module Data.Void.Base where

-- An empty type is a type with no constructors. We call the "official" one
-- Void. It is the initial object (up to isomorphism) in the category Sets.
data Void : Set where

-- The absurd function is evidence that Void satisfies the universal property
-- of initial objects in the categry Sets. You can also think of it as the
-- fold operation for Void.
absurd : {X : Set} -> Void -> X
absurd ()
