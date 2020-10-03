{-# OPTIONS --type-in-type #-}

module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.List as List using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

repack : (List Char -> List Char) -> String -> String
repack f = pack <<< f <<< unpack

cons : Char -> String -> String
cons c = repack (c ::_)

singleton : Char -> String
singleton = pack <<< [_]

snoc : String -> Char -> String
snoc s c = repack (_<> [ c ]) s

head : String -> Maybe Char
head s with unpack s
... | [] = Nothing
... | (c :: _) = Just c

tail : String -> Maybe String
tail s with unpack s
... | [] = Nothing
... | (_ :: cs) = Just (pack cs)

uncons : String -> Maybe (Char * String)
uncons s with unpack s
... | [] = Nothing
... | (c :: cs) = Just (c , pack cs)

reverse : String -> String
reverse = repack List.reverse

intersperse : Char -> String -> String
intersperse = repack <<< List.intersperse

takeWhile : (Char -> Bool) -> String -> String
takeWhile = repack <<< List.takeWhile

dropWhile : (Char -> Bool) -> String -> String
dropWhile = repack <<< List.dropWhile

take : Nat -> String -> String
take = repack <<< List.take

drop : Nat -> String -> String
drop = repack <<< List.drop

deleteAt : Nat -> String -> String
deleteAt = repack <<< List.deleteAt

modifyAt : Nat -> (Char -> Char) -> String -> String
modifyAt n = repack <<< List.modifyAt n

setAt : Nat -> Char -> String -> String
setAt n = repack <<< List.setAt n

insertAt : Nat -> Char -> String -> String
insertAt n = repack <<< List.insertAt n

isPrefixOf : String -> String -> Bool
isPrefixOf s s' = List.isPrefixOf (unpack s) (unpack s')

isSuffixOf : String -> String -> Bool
isSuffixOf s s' = List.isSuffixOf (unpack s) (unpack s')

isInfixOf : String -> String -> Bool
isInfixOf s s' = List.isInfixOf (unpack s) (unpack s')

isSubsequenceOf : String -> String -> Bool
isSubsequenceOf s s' = List.isSubsequenceOf (unpack s) (unpack s')

length : String -> Nat
length = List.length <<< unpack

filter : (Char -> Bool) -> String -> String
filter = repack <<< List.filter

partition : (Char -> Bool) -> String -> String * String
partition p s = bimap pack pack (List.partition p (unpack s))

replicate : Nat -> String -> String
replicate n s = fold (List.replicate n s)

padRight : Nat -> Char -> String -> String
padRight l c s =
  s <> replicate (l - length s) (singleton c)

padLeft : Nat -> Char -> String -> String
padLeft l c s =
  replicate (l - length s) (singleton c) <> s

break : (Char -> Bool) -> String -> String * String
break p s = bimap pack pack $ List.break p (unpack s)

{-# TERMINATING #-}
words : String -> List String
words s = let s' = dropWhile isSpace s in
  if s' == ""
    then []
    else let (w , s'') = break isSpace s' in w :: words s''

unwords : List String -> String
unwords [] = ""
unwords (w :: ws) = w <> go ws
  where
    go : List String -> String
    go [] = ""
    go (v :: vs) = " " <> v <> go vs

lines : String -> List String
lines s =
  let
    (l , ls) = foldl f ("" , []) (unpack s)
  in
    List.reverse (if l == "" then ls else (l :: ls))
  where
    f : String * List String -> Char -> String * List String
    f (l , ls) '\n' = ("" , l :: ls)
    f (l , ls) c = (snoc l c , ls)

unlines : List String -> String
unlines = fold <<< map (_<> "\n")

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC cons = Text.cons #-}
{-# COMPILE GHC singleton = Text.singleton #-}
{-# COMPILE GHC snoc = Text.snoc #-}
{-# COMPILE GHC reverse = Text.reverse #-}
{-# COMPILE GHC intersperse = Text.intersperse #-}
{-# COMPILE GHC takeWhile = Text.takeWhile #-}
{-# COMPILE GHC dropWhile = Text.dropWhile #-}
{-# COMPILE GHC take = Text.take . fromInteger #-}
{-# COMPILE GHC drop = Text.drop . fromInteger #-}
{-# COMPILE GHC isPrefixOf = Text.isPrefixOf #-}
{-# COMPILE GHC isSuffixOf = Text.isSuffixOf #-}
{-# COMPILE GHC isInfixOf = Text.isInfixOf #-}
{-# COMPILE GHC length = toInteger. Text.length #-}
{-# COMPILE GHC filter = Text.filter #-}
{-# COMPILE GHC break = Text.break #-}
{-# COMPILE GHC words = Text.words #-}
{-# COMPILE GHC unwords = Text.unwords #-}
{-# COMPILE GHC lines = Text.lines #-}
{-# COMPILE GHC unlines = Text.unlines #-}
{-# COMPILE GHC replicate = Text.replicate . fromInteger #-}
