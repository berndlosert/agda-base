open import Prelude
open import Data.Enum
open import Data.Foldable
open import System.IO

fizz buzz num fizzbuzz : Nat -> Maybe String
fizz n = if n % 3 == 0 then just "Fizz" else nothing
buzz n = if n % 5 == 0 then just "Buzz" else nothing
num n = just (show n)
fizzbuzz n = fizz n <> buzz n <|> num n

main : IO Unit
main =
  for* (enumFromTo 1 100) \ n ->
    putStrLn (fromJust (fizzbuzz n) {{trustMe}})
