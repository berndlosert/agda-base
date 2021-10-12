{-# OPTIONS --type-in-type #-}

open import Prelude

open import Data.Enum
open import Data.Foldable as Foldable using ()
open import Data.List as List using ()
open import Data.String as String using ()

reverseTest :
  List.reverse ('a' :: 'b' :: 'c' :: []) === 'c' :: 'b' :: 'a' :: []
reverseTest = refl

groupTest :
  List.group
    (String.unpack "Mississippi")
  ===
  map String.unpack
    ("M" :: "i" :: "ss" :: "i" :: "ss" :: "i" :: "pp" :: "i" :: [])
groupTest = refl

breakOnTest1 :
  List.breakOn
    (String.unpack "::")
    (String.unpack "a::b::c")
  ===
    (String.unpack "a" , String.unpack "::b::c")
breakOnTest1 = refl

breakOnTest2 :
  List.breakOn
    (String.unpack "/")
    (String.unpack "foobar")
  ===
    (String.unpack "foobar", [])
breakOnTest2 = refl

chunksOfTest :
  List.chunksOf 3 (enumFromTo {Nat} 1 10)
  ===
  (1 :: 2 :: 3 :: [])
  :: (4 :: 5 :: 6 :: [])
  :: (7 :: 8 :: 9 :: [])
  :: (10 :: [])
  :: []
chunksOfTest = refl

testWords :
  String.words "abc 123  xyz "
  ===
  "abc" :: "123" :: "xyz" :: []
testWords = refl

testFirst :
  List.first (enumFromTo {Nat} 1 100000000)
  ===
  just 1
testFirst = refl

testEnumFromTo :
  (enumFromTo {Nat} 1 20)
  ===
  the Nat 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: 18 :: 19 :: 20 :: []
testEnumFromTo = refl

last : {a : Set} -> List a -> Maybe a
last [] = nothing
last (x :: []) = just x
last (x :: xs) = last xs

testLast :
  last (enumFromTo {Int} 1 100)
  ===
  just 100
testLast = refl

