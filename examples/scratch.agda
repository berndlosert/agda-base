open import Prelude

open import System.IO

postulate
  foo : Set (1 lmax 2 lmax 3)

main : IO Unit
main = putStrLn "❤"
