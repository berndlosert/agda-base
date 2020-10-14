{-# OPTIONS --type-in-type #-}

module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (pack; unpack; empty)

open import Data.Constraint.Nonempty
open import Data.List as List using ()

-------------------------------------------------------------------------------
-- Creation and elimination
-------------------------------------------------------------------------------

Chars : Set
Chars = List Char

pack : Chars -> String
pack = Prelude.pack

unpack : String -> Chars
unpack = Prelude.unpack

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
uncons s = maybe Nothing (Just <<< second pack) (List.uncons (unpack s))

unsnoc : String -> Maybe (String * Char)
unsnoc s = maybe Nothing (Just <<< first pack) (List.unsnoc (unpack s))

head : String -> Maybe Char
head s = map fst (uncons s)

tail : String -> Maybe String
tail s = map snd (uncons s)

length : String -> Nat
length = List.length <<< unpack

init : (s : String) {{_ : Nonempty s}} -> String
init s = pack $ List.init (unpack s) {{believeMe}}

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
-- Breaking strings
-------------------------------------------------------------------------------

takeWhile : (Char -> Bool) -> String -> String
takeWhile p s = pack $ List.takeWhile p $ unpack s

dropWhile : (Char -> Bool) -> String -> String
dropWhile p s = pack $ List.dropWhile p $ unpack s

span : (Char -> Bool) -> String -> String * String
span p s = bimap pack pack $ List.span p $ unpack s

break : (Char -> Bool) -> String -> String * String
break p s = bimap pack pack $ List.break p $ unpack s

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC takeWhile = Text.takeWhile #-}
{-# COMPILE GHC dropWhile = Text.dropWhile #-}
{-# COMPILE GHC span = Text.span #-}
{-# COMPILE GHC break = Text.break #-}

-------------------------------------------------------------------------------
-- Breaking into lines and words
-------------------------------------------------------------------------------

{-# TERMINATING #-}
words : String -> List String
words s = map pack $ words' $ unpack s
  where
    words' : Chars -> List (Chars)
    words' cs with List.dropWhile isSpace cs
    ... | [] = []
    ... | cs' = let (w , cs'') = List.break isSpace cs' in w :: words' cs''

unwords : List String -> String
unwords [] = ""
unwords (w :: ws) = w <> go ws
  where
    go : List String -> String
    go [] = ""
    go (v :: vs) = " " <> v <> go vs

lines : String -> List String
lines s = map pack $ lines' $ unpack s
  where
    lines' : Chars -> List (Chars)
    lines' cs =
      let (l , ls) = List.foldl f ([] , []) cs
      in List.reverse (if l == [] then ls else (l :: ls))
      where
        f : Chars * List (Chars) -> Char -> Chars * List (Chars)
        f (l , ls) '\n' = ([] , l :: ls)
        f (l , ls) c = (List.snoc l c , ls)

unlines : List String -> String
unlines = List.fold <<< map (_<> "\n")

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC words = Text.words #-}
{-# COMPILE GHC unwords = Text.unwords #-}
{-# COMPILE GHC lines = Text.lines #-}
{-# COMPILE GHC unlines = Text.unlines #-}
