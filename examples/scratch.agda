open import Prelude

open import Control.Monad.Either.Trans
open import Data.Enum
open import Data.Functor.Identity
open import Data.Map
open import Data.Functor.Recursive
open import System.IO

foo1 : List Nat
foo1 = enumFromTo 3 14

foo2 : List Nat
foo2 = enumFromTo 17 5

foo3 : List Int
foo3 = enumFromTo -13 7

foo4 : List Int
foo4 = enumFromTo 8 29

foo5 : EitherT String Identity (Map Nat Bool)
foo5 = asEitherT $ asIdentity $ right $ fromList $ (1 , false) :: (2 , true) :: []

foo6 : Fix (NatF)
foo6 = asFix (suc (asFix zero))

main : IO Unit
main = do
  print foo1
  print foo2
  print foo3
  print foo4
  print foo5
  print foo6
