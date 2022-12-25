open import Prelude

open import Control.Monad.Codensity
open import Data.Subset as Subset using (Subset)
open import System.IO

foo1 : Subset Nat
foo1 = Subset.fromList (1 :: 1 :: 2 :: 2 :: [])

foo2 : Subset Nat
foo2 = Subset.fromList (3 :: 3 :: 4 :: 4 :: [])

bar2 : Codensity Ord Subset Nat
bar2 = do
  x <- liftCodensity foo1
  y <- liftCodensity foo2
  pure (x + y)

main : IO Unit
main = do
  print (lowerCodensity bar2)