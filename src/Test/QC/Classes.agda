module Test.QC.Classes where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Gen
open import Control.Monad.IO.Class
open import Data.Monoid.Foldable
open import Data.String.Show
open import Properties.Eq
open import Properties.Functor
open import Properties.Monoid
open import Properties.Semigroup
open import System.IO
open import Test.QC
open import Test.QC.Fun
open import Test.QC.Poly

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Laws
-------------------------------------------------------------------------------

record Laws : Type where
  constructor laws
  field
    typeclass : String
    type : String
    properties : List Test

open Laws

lawsCheck : Laws -> IO Unit
lawsCheck (laws typeclass type properties) = for! properties \ where
  theTest ->
    let newTestName = typeclass <> "-" <> type <> ": " <> testName theTest
    in quickCheck record theTest { testName = newTestName }

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

module _  {{_ : Show a}} {{_ : Eq a}} (gen : Gen a)  where

  eqReflexive : Test
  eqReflexive = test "reflexivity" (| reflexivity gen |)

  eqSymmetric : Test
  eqSymmetric = test "symmetry" (| symmetry gen gen |)

  eqTransitive : Test
  eqTransitive = test "transitivity" (| transitivity gen gen gen |)

  eqNegation : Test
  eqNegation = test "negation" (| negation gen gen |)

  eqLaws : List Test
  eqLaws =
    eqTransitive
      :: eqSymmetric
      :: eqReflexive
      :: eqNegation
      :: []

-------------------------------------------------------------------------------
-- Semigroup
-------------------------------------------------------------------------------

module _  {{_ : Show a}} {{_ : Semigroup a}} {{_ : Eq a}} (gen : Gen a)  where

  semigroupAssociativity : Test
  semigroupAssociativity =
    test "semigroupAssociativity" (| associativity gen gen gen |)

  semigroupLaws : List Test
  semigroupLaws = semigroupAssociativity :: []

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

module _  {{_ : Show a}} {{_ : Monoid a}} {{_ : Eq a}} (gen : Gen a)  where

  monoidLeftIdentity : Test
  monoidLeftIdentity = test "monoidLeftIdentity" (| leftIdentity gen |)

  monoidRightIdentity : Test
  monoidRightIdentity = test "monoidRightIdentity" (| rightIdentity gen |)

monoidLaws : {{_ : Show a}} {{_ : Monoid a}} {{_ : Eq a}}
  -> (gen : Gen a) -> List Test
monoidLaws gen = semigroupLaws gen <>
  monoidLeftIdentity gen :: monoidRightIdentity gen :: []

-------------------------------------------------------------------------------
-- Functor
-------------------------------------------------------------------------------

module _  {{_ : Functor f}} (gen : Gen (f A)) where

  functorComposition : {{Eq (f C)}} -> Test
  functorComposition =
    let
      genAB = genFun genA genB
      genBC = genFun genB genC
    in test "functorComposition"
      (| preservesComposition (applyFun <$> genAB) (applyFun <$> genBC) gen |)

  functorIdentity : {{Eq (f A)}} -> Test
  functorIdentity = test "functorIdentity"
    (| preservesIdentity gen |)

  functorLaws : {{Eq (f C)}} -> {{Eq (f A)}} -> List Test
  functorLaws =
    functorComposition
      :: functorIdentity
      :: []