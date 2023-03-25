module Test.QC.Classes where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.String.Show
open import System.IO
open import Test.QC

-------------------------------------------------------------------------------
-- Laws
-------------------------------------------------------------------------------

record Laws : Set where
  field
    typeclass : String
    properties : List (Pair String Property)

open Laws

lawsCheck : Laws -> IO Unit
lawsCheck laws = do
  flip foldMap (properties laws) \ where
    (name , p) -> do
      putStr (typeclass laws <> ": " <> name <> " ")
      quickCheck p

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

module _ (a : Set) {{_ : Eq a}} {{_ : Arbitrary a}} {{_ : Show a}} where
  eqReflexive : Property
  eqReflexive = property p
    where
      p : a -> Bool
      p x = x == x

  eqSymmetric : Property
  eqSymmetric = property p
    where
      p : a -> a -> Bool
      p x y = case x == y of \ where
        true -> y == x
        false -> y /= x

  eqTransitive : Property
  eqTransitive = property p
    where
      p : a -> a -> a -> Bool
      p x y z = case x == y of \ where
        true -> case y == z of \ where
          true -> x == z
          false -> x /= z
        false -> case y == z of \ where
          true -> x /= y
          false -> true

  eqNegation : Property
  eqNegation = property p
    where
      p : a -> a -> Bool
      p x y = (x /= y) == not (x == y)

  eqLaws : Laws
  eqLaws .typeclass = "Eq"
  eqLaws .properties =
    ("Transitive", eqTransitive)
      :: ("Symmetric", eqSymmetric)
      :: ("Reflexive", eqReflexive)
      :: []
