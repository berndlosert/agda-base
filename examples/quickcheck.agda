open import Prelude

open import Control.Monad.Gen
open import Data.List as List using ()
open import Data.Monoid.Sum
open import System.IO
open import Test.QC
open import Test.QC.Classes
open import Test.QC.Fun
open import Test.QC.Poly

instance
  _ = FromNat-Int

propRevApp : Test
propRevApp = test "check reverse is monoid homomorphism" (| prop gen gen |)
  where
    gen : Gen (List Nat)
    gen = genListOfSize 10 (genNatBetween 1 100)

    prop : List Nat -> List Nat -> Bool
    prop xs ys = List.reverse (xs <> ys) == List.reverse xs <> List.reverse ys

main : IO Unit
main = do
  quickCheck propRevApp
  lawsCheck $ laws "Eq" "Int" $ eqLaws $ genIntBetween 1 100
  lawsCheck $ laws "Monoid" "Sum Int" $ monoidLaws $ map asSum $ genIntBetween 1 100
  lawsCheck $ laws "Functor" "List" $ functorLaws $ genListOfSize 5 genA