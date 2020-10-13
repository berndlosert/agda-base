{-# OPTIONS --type-in-type #-}

module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (pack; unpack; empty)

open import Data.List as List using ()
open import Control.Lens

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
singleton = pack <<< [_]

empty : String
empty = ""

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC singleton = Text.singleton #-}

-------------------------------------------------------------------------------
-- Basic interface
-------------------------------------------------------------------------------

cons : Char -> String -> String
cons c = under packed (c ::_)

snoc : String -> Char -> String
snoc s c = under packed (_<> [ c ]) s

append : String -> String -> String
append = _<>_

uncons : String -> Maybe (Char * String)
uncons s = maybe Nothing (Just <<< second pack) (List.uncons (unpack s))

unsnoc : String -> Maybe (String * Char)
unsnoc s = maybe Nothing (Just <<< first pack) (List.unsnoc (unpack s))

head : String -> Maybe Char
head = map fst <<< uncons

tail : String -> Maybe String
tail = map snd <<< uncons

length : String -> Nat
length = List.count <<< unpack

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
reverse = under packed List.reverse

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
-- Breaking into lines and words
-------------------------------------------------------------------------------

{-# TERMINATING #-}
words : String -> List String
words = unpacked words'
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
lines = unpacked lines'
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
