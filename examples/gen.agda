open import Prelude

open import Control.Monad.Gen
open import Data.Enum
open import Data.Word
open import System.IO
open import System.Random
open import System.Time

ns : List Nat
ns = enumFromTo 2 16

test : Gen Bool
test = do
  n <- genNatBetween 1 10
  pure (n <= 10)

check : Nat -> Gen Bool -> Gen String
check 0 _ = pure "all tests passed"
check (suc n) gen = do
  b <- gen
  if b then check n gen else pure "failed"

main : IO Unit
main = do
  rng <- getStdGen
  print (snd (runGen (check 100 test) rng))