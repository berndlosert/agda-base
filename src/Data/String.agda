{-# OPTIONS --type-in-type #-}

module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.List as List using ()
open import Control.Lens

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

Chars : Set
Chars = List Char

cons : Char -> String -> String
cons c = under packed (c ::_)

snoc : String -> Char -> String
snoc s c = under packed (_<> [ c ]) s

replicate : Nat -> String -> String
replicate n s = List.fold (List.replicate n s)

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

uncons : String -> Maybe (Char * String)
uncons s = maybe Nothing (Just <<< second pack) (List.uncons (unpack s))

head : String -> Maybe Char
head = map fst <<< uncons

tail : String -> Maybe String
tail = map snd <<< uncons

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

length : String -> Nat
length = List.count <<< unpack

padRight : Nat -> Char -> String -> String
padRight l c s = s <> replicate (l - length s) (cons c "")

padLeft : Nat -> Char -> String -> String
padLeft l c = under packed (padLeft' l c)
  where
    padLeft' : Nat -> Char -> Chars -> Chars
    padLeft' l c cs = List.replicate (l - List.count cs) c <> cs

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

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC cons = Text.cons #-}
{-# COMPILE GHC snoc = Text.snoc #-}
{-# COMPILE GHC uncons = Text.uncons #-}
{-# COMPILE GHC replicate = \ n -> Text.replicate (fromInteger n) #-}
{-# COMPILE GHC length = toInteger . Text.length #-}
{-# COMPILE GHC words = Text.words #-}
{-# COMPILE GHC unwords = Text.unwords #-}
{-# COMPILE GHC lines = Text.lines #-}
{-# COMPILE GHC unlines = Text.unlines #-}
