open import Prelude
open import Data.Enum
open import Data.Foldable
open import Data.String.Show
open import System.IO

fizz buzz num fizzbuzz : Nat -> Maybe String
fizz n = if mod n 3 == 0 then "Fizz"
buzz n = if mod n 5 == 0 then "Buzz"
num n = just (show n)
fizzbuzz n = fizz n <> buzz n <|> num n

main : IO Unit
main =
  for* (enumFromTo 1 100) \ n ->
    putStrLn (fromJust (fizzbuzz n))
