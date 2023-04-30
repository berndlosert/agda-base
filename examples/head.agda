open import Prelude

open import Data.Monoid.Foldable
open import System.IO

data Safety (b : Bool) : Type where
  safe : Safety b
  safest : Safety b
  unsafe : Safety b

Result : {b : Bool} -> Safety b -> Type -> Type
Result safe a = Maybe a
Result {b} safest a = {{Assert b}} -> a
Result unsafe a = a

head : {a : Type} (xs : List a) (s : Safety (notNull xs)) -> Result s a
head [] safe = nothing
head (x :: _) safe = just x
head (x :: _) safest = x
head [] unsafe = undefined
head (x :: _) unsafe = x

-- Does not work because of asAny problem with metavariables not in scope.
safe' : {a c : Type} {b : Bool} -> (a -> (s : Safety b) -> Result s c) -> a -> Result {b} safe c
safe' f x = f x safe

chars : List Char
chars = 'h' :: 'e' :: 'a' :: 'd' :: []

test : Maybe Char
test = head chars safe

test1 : Char
test1 = head chars safest

test2 : Char
test2 = head chars unsafe

main : IO Unit
main = do
  print test
  print test1
  print test2