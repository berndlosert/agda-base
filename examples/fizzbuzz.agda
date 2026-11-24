open import Control.Applicative using (when)
open import Control.Monad using (Monad; _>>=_; _>>_)
open import Control.Monad.Instances using (Monad-Identity)
open import Control.Monad.State
open import Control.Semigroupoid using (_<<<_)
open import Data.Enum
open import Data.Monoid.Foldable
open import Data.Semigroup using (_<>_)
open import Data.Show
open import Prelude
open import System.IO

fizzbuzz : Nat -> String
fizzbuzz n = flip execState "" do
  when (mod n 3 == 0) (put "Fizz")
  when (mod n 5 == 0) (modify (_<> "Buzz"))
  str <- get
  when (str == "") (put (show n))

main : IO Unit
main = for! (enumFromTo 1 100) (putStrLn <<< fizzbuzz)
