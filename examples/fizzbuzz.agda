open import Prelude

open import Control.Monad.State
open import Data.Enum
open import Data.Monoid.Foldable
open import Data.String.Show
open import System.IO

fizzbuzz : Nat -> String
fizzbuzz n = flip execState "" do
  when (mod n 3 == 0) (put "Fizz")
  when (mod n 5 == 0) (modify (_<> "Buzz"))
  str <- get
  when (str == "") (put (show n))

main : IO Unit
main = for! (enumFromTo 1 100) (putStrLn <<< fizzbuzz)
