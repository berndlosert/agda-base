{-# OPTIONS --type-in-type #-}

module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.List

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

padRight : Nat -> Char -> String -> String
padRight l c cs = cs <> replicate (l - count cs) c

padLeft : Nat -> Char -> String -> String
padLeft l c cs = replicate (l - count cs) c <> cs

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
    reverse (if l == "" then ls else (l :: ls))
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
{-# COMPILE GHC words = Text.words #-}
{-# COMPILE GHC unwords = Text.unwords #-}
{-# COMPILE GHC lines = Text.lines #-}
{-# COMPILE GHC unlines = Text.unlines #-}
