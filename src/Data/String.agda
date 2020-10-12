{-# OPTIONS --type-in-type #-}

module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.List
open import Control.Lens

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

Chars : Set
Chars = List Char

padRight : Nat -> Char -> String -> String
padRight l c = under packed (padRight' l c)
  where
    padRight' : Nat -> Char -> Chars -> Chars
    padRight' l c cs = cs <> replicate (l - count cs) c

padLeft : Nat -> Char -> String -> String
padLeft l c = under packed (padLeft' l c)
  where
    padLeft' : Nat -> Char -> Chars -> Chars
    padLeft' l c cs = replicate (l - count cs) c <> cs

{-# TERMINATING #-}
words : String -> List String
words = unpacked words'
  where
    words' : Chars -> List (Chars)
    words' cs with dropWhile isSpace cs
    ... | [] = []
    ... | cs' = let (w , cs'') = break isSpace cs' in w :: words' cs''

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
      let (l , ls) = foldl f ([] , []) cs
      in reverse (if l == [] then ls else (l :: ls))
      where
        f : Chars * List (Chars) -> Char -> Chars * List (Chars)
        f (l , ls) '\n' = ([] , l :: ls)
        f (l , ls) c = (snoc l c , ls)

unlines : List String -> String
unlines = fold <<< map (_<> "\n")

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC words = Text.words #-}
{-# COMPILE GHC unwords = Text.unwords #-}
{-# COMPILE GHC lines = Text.lines #-}
{-# COMPILE GHC unlines = Text.unlines #-}
