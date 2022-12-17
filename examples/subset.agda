open import Prelude

open import Control.Monad.Normal
open import Data.Subset as Subset using (Subset)
open import System.IO

foo1 : Subset Nat
foo1 = Subset.fromList (1 :: 1 :: 2 :: 2 :: [])

foo2 : Subset Nat
foo2 = Subset.fromList (3 :: 3 :: 4 :: 4 :: [])

bar1 : Subset Nat
bar1 = let _>>=_ = Subset._>>=_; _>>_ = Subset._>>_ in do
  x <- foo1
  y <- foo2
  Subset.singleton (x + y)

bar2 : NM Ord Subset Nat
bar2 = do
  x <- liftNM foo1
  y <- liftNM foo2
  pure (x + y)

main : IO Unit
main = do
  print bar1
  print (lowerNM Subset.singleton Subset._>>=_ bar2)