{-# OPTIONS --type-in-type #-}

module Data.Tree.Finger.Split where

-------------------------------------------------------------------------------
-- Split
-------------------------------------------------------------------------------

data Split (f : Set -> Set) (a : Set) : Set where
  Split: : f a -> a -> f a -> Split f a
