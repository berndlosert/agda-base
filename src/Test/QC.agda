module Test.QC where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Either.Trans
open import Control.Monad.Error.Class
open import Control.Monad.Gen
open import Control.Monad.IO.Class
open import Data.List as List using ()
open import Data.String as String using ()
open import Data.String.Show
open import System.IO
open import System.Random

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.IO.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    m : Type -> Type

-------------------------------------------------------------------------------
-- Test
-------------------------------------------------------------------------------

record Test : Type where
  constructor test
  field
    testName : String
    testCode : Gen Bool

open Test public

-------------------------------------------------------------------------------
-- Test runners
-------------------------------------------------------------------------------

testRunner : StdGen -> Nat -> Test -> IO Unit
testRunner rng0 n (test name code) = go n rng0
  where

    nextB : StdGen -> Tuple StdGen Bool
    nextB = runGen code

    go : Nat -> StdGen -> IO Unit
    go 0 _ = putStrLn ("[OK] " <> name)
    go (suc n) rng = do
      let (rng1 , testPassed) = nextB rng
      if testPassed
        then go n rng1
        else putStrLn ("[FAILED] " <> name <> "\n")

check : Nat -> Test -> IO Unit
check maxTest theTest = do
  rng <- liftIO newStdGen
  testRunner rng maxTest theTest

quickCheck : Test -> IO Unit
quickCheck = check 100
