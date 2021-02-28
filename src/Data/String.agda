{-# OPTIONS --type-in-type #-}

module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.List as List using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Creation and elimination
-------------------------------------------------------------------------------

singleton : Char -> String
singleton c = pack [ c ]

empty : String
empty = ""

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC singleton = Text.singleton #-}

-------------------------------------------------------------------------------
-- Basic interface
-------------------------------------------------------------------------------

cons : Char -> String -> String
cons c s = pack $ c ::_ $ unpack s

snoc : String -> Char -> String
snoc s c = s <> singleton c

append : String -> String -> String
append = _<>_

uncons : String -> Maybe (Char * String)
uncons s = map pack <$> List.uncons (unpack s)

unsnoc : String -> Maybe (String * Char)
unsnoc s = lmap pack <$> List.unsnoc (unpack s)

head : String -> Maybe Char
head s = map fst (uncons s)

tail : String -> Maybe String
tail s = map snd (uncons s)

length : String -> Nat
length = List.length <<< unpack

init : (s : String) {{_ : IsNonempty s}} -> String
init s = pack $ List.init (unpack s) {{trustMe}}

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC cons = Text.cons #-}
{-# COMPILE GHC snoc = Text.snoc #-}
{-# COMPILE GHC uncons = Text.uncons #-}
{-# COMPILE GHC unsnoc = Text.unsnoc #-}
{-# COMPILE GHC length = toInteger . Text.length #-}

-------------------------------------------------------------------------------
-- Generation and unfolding
-------------------------------------------------------------------------------

replicate : Nat -> String -> String
replicate n s = List.fold (List.replicate n s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC replicate = Text.replicate . fromInteger #-}

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : String -> String
reverse s = pack $ List.reverse $ unpack s

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC reverse = Text.reverse #-}

-------------------------------------------------------------------------------
-- Justification
-------------------------------------------------------------------------------

justifyLeft : Nat -> Char -> String -> String
justifyLeft l c s = s <> replicate (l - length s) (singleton c)

justifyRight : Nat -> Char -> String -> String
justifyRight l c s = replicate (l - length s) (singleton c) <> s

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC justifyLeft = Text.justifyLeft . fromInteger #-}
{-# COMPILE GHC justifyRight = Text.justifyRight . fromInteger #-}

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

foldl : (a -> Char -> a) -> a -> String -> a
foldl f z s = List.foldl f z (unpack s)

-------------------------------------------------------------------------------
-- Breaking strings
-------------------------------------------------------------------------------

take : Nat -> String -> String
take n s = pack $ List.take n $ unpack s

takeWhile : (Char -> Bool) -> String -> String
takeWhile p s = pack $ List.takeWhile p $ unpack s

drop : Nat -> String -> String
drop n s = pack $ List.drop n $ unpack s

dropWhile : (Char -> Bool) -> String -> String
dropWhile p s = pack $ List.dropWhile p $ unpack s

span : (Char -> Bool) -> String -> String * String
span p s = bimap pack pack $ List.span p $ unpack s

break : (Char -> Bool) -> String -> String * String
break p s = bimap pack pack $ List.break p $ unpack s

breakOn : String -> String -> String * String
breakOn delim s = bimap pack pack $ List.breakOn (unpack delim) (unpack s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC take = Text.take . fromInteger #-}
{-# COMPILE GHC takeWhile = Text.takeWhile #-}
{-# COMPILE GHC drop = Text.drop . fromInteger #-}
{-# COMPILE GHC dropWhile = Text.dropWhile #-}
{-# COMPILE GHC span = Text.span #-}
{-# COMPILE GHC break = Text.break #-}
{-# COMPILE GHC breakOn = Text.breakOn #-}

-------------------------------------------------------------------------------
-- Breaking into many substrings
-------------------------------------------------------------------------------

splitOn : (delim : String) {{_ : IsNonempty delim}} -> String -> List String
splitOn delim s =
  map pack $ List.splitOn (unpack delim) {{trustMe}} (unpack s)

split : (Char -> Bool) -> String -> List String
split f s = map pack $ List.split f (unpack s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC split = Text.split #-}

-------------------------------------------------------------------------------
-- Breaking into lines and words
-------------------------------------------------------------------------------

{-# TERMINATING #-}
words : String -> List String
words s = let s' = dropWhile isSpace s in
  if s' == ""
    then []
    else let (w , s'') = break isSpace s' in (w :: words s'')

unwords : List String -> String
unwords [] = ""
unwords (w :: ws) = w <> go ws
  where
    go : List String -> String
    go [] = ""
    go (v :: vs) = " " <> v <> go vs

lines : String -> List String
lines s =
  let (l , ls) = foldl f ("" , []) s
  in List.reverse (if l == "" then ls else (l :: ls))
  where
    f : String * List String -> Char -> String * List String
    f (l , ls) '\n' = ("" , l :: ls)
    f (l , ls) c = (snoc l c , ls)

unlines : List String -> String
unlines = List.fold <<< map (_<> "\n")

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC words = Text.words #-}
{-# COMPILE GHC unwords = Text.unwords #-}
{-# COMPILE GHC lines = Text.lines #-}
{-# COMPILE GHC unlines = Text.unlines #-}
