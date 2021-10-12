{-# OPTIONS --type-in-type #-}

open import Prelude

open import Control.Recursion.General

fact : Rec Nat Nat
fact 0 = pure 1
fact 1 = pure 1
fact (suc n) = do
  res <- call n -- fact n
  pure (suc n * res)

test0 : combust fact 0 === 1
test0 = refl

test1 : combust fact 1 === 1
test1 = refl

test5 : combust fact 5 === 120
test5 = refl

testPetrol1 : petrol fact 3 5 === nothing
testPetrol1 = refl

testPetrol2 : petrol fact 4 5 === just 120
testPetrol2 = refl
