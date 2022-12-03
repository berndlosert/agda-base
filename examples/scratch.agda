open import Prelude

open import Control.Monad.Either.Trans
open import Data.Enum
open import Data.Functor.Identity
open import Data.Map
open import Data.Functor.Recursive
open import System.IO

variable
  a : Set

foo1 : List Nat
foo1 = enumFromTo 3 14

foo2 : List Nat
foo2 = enumFromTo 17 5

foo3 : List Int
foo3 = coerce foo2

foo4 : List Int
foo4 = enumFromTo 8 29

foo5 : EitherT String Identity (Map Nat Bool)
foo5 = asEitherT $ asIdentity $ right $ fromList $ (1 , false) :: (2 , true) :: []

foo6 : Fix (NatF)
foo6 = asFix (suc (asFix zero))

record CounterF (r : Set) : Set where
  field
    get : Nat
    inc : r

Counter : Set
Counter = Fix CounterF

newCounter : Nat -> Counter
newCounter n = asFix \ where
  .CounterF.get -> n
  .CounterF.inc -> newCounter (suc n)

get : Counter -> Nat
get (asFix c) = CounterF.get c

inc : Counter -> Counter
inc (asFix c) = CounterF.inc c

foo7 : Counter
foo7 = newCounter 10

data Stream (a : Set) : Set where
  cons : a -> Stream a -> Stream a

ones : Stream Nat
ones = cons 1 ones

take : Nat -> Stream a -> List a
take 0 _ = []
take (suc n) (cons a s) = a :: take n s

Foo : Set -> Set
Foo = \ a -> Maybe a

foo : Foo Int
foo = just 10

x y z : Identity Nat
x = asIdentity 1
y = asIdentity 2
z = asIdentity 3

foo8 : List Nat
foo8 = coerce (x :: y :: z :: [])

foo9 : List (Identity Nat)
foo9 = coerce foo8

Bar : Set
Bar = forall (a : Set) -> Maybe a

-- bar : Bar Int -- oops
bar : Bar
bar = \ _ -> just undefined

main : IO Unit
main = do
  print foo1
  print foo2
  print foo3
  print foo4
  print foo5
  print foo6
  print (get (inc foo7))
  print (take 7 ones)
  print foo8
  print foo9
