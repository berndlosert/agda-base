open import Prelude

open import Control.Monad.ST
open import Data.Monoid.Foldable
open import Data.STRef
open import System.IO

sumST : List Nat -> Nat
sumST xs = runST do           -- runST takes out stateful code and makes it pure again.

    n <- newSTRef 0           -- Create an STRef (place in memory to store values)

    for! xs \ x -> do         -- For each element of xs ..
      modifySTRef n (_+ x)    -- add it to what we have in n.

    readSTRef n               -- read the value of n, and return it.

main : IO Unit
main = print (sumST (1 :: 3 :: 6 :: 19 :: []))