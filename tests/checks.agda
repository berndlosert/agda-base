open import Prelude

open import Data.Enum
open import Data.Foldable
open import Data.List as List using ()
open import Data.String as String using ()

avg : List Float -> Float
avg = (| sum / length |)

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

testEnumFromTo :
  (enumFromTo {Int} 1 20)
  ===
  the Int 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: 18 :: 19 :: 20 :: []
testEnumFromTo = refl

testFirst :
  List.first (enumFromTo {Nat} 1 100000000)
  ===
  just 1
testFirst = refl

testLast :
  List.last (enumFromTo {Int} 1 1000)
  ===
  just 1000
testLast = refl

testPermutations :
  List.permutations (the Nat 1 :: 2 :: 3 :: [])
  ===
  (1 :: 2 :: 3 :: []) :: (1 :: 3 :: 2 :: []) :: (2 :: 1 :: 3 :: []) :: (2 :: 3 :: 1 :: []) :: (3 :: 1 :: 2 :: []) :: (3 :: 2 :: 1 :: []) :: []
testPermutations = refl
