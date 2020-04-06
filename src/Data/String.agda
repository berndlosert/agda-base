{-# OPTIONS --type-in-type #-}

module Data.String where

import Data.List as List

open import Agda.Builtin.String public using (String)
open import Agda.Builtin.String public renaming (primStringToList to unpack)
open import Agda.Builtin.String public renaming (primStringFromList to pack)
open import Data.Bool using (Bool)
open import Data.Eq using (Eq)
open import Data.Eq public using (_==_; _/=_)
open import Data.Char using (Char)
open import Data.Foldable using (Fold)
open import Data.Foldable public using (foldMap)
open import Data.Functor using (map; _<$>_)
open import Data.Function using (_<<<_; _>>>_)
open import Data.Monoid using (Monoid; mempty)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (Nat)
open import Data.Pair using (Pair; _,_; fst; snd)
open import Data.Semigroup using (Semigroup)
open import Data.Semigroup public using (_<>_)
open List using (List; _::_; [])

instance
  eqString : Eq String
  eqString ._==_ = Agda.Builtin.String.primStringEquality

  --isStringString : IsString String
  --isStringString = record {
  --    Constraint = const Unit;
  --    fromString = \ s -> s
  --  }

  semigroupString : Semigroup String
  semigroupString ._<>_ = Agda.Builtin.String.primStringAppend

  monoidString : Monoid String
  monoidString .mempty = ""

  foldStringChar : Fold String Char
  foldStringChar .foldMap f = foldMap f <<< unpack

fromChar : Char -> String
fromChar c = pack (List.pure c)

length : String -> Nat
length = unpack >>> List.length

startsWith : String -> String -> Bool
startsWith s s' = List.isPrefixOf (unpack s) (unpack s')

stripPrefix : String -> String -> Maybe String
stripPrefix s s' = pack <$> List.stripPrefix (unpack s) (unpack s')

--padRight : Nat -> Char -> String -> String
--padRight desiredLength padChar s =
--  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
--  in s ++ (List.foldl _++_ "" replicated)
--
--padLeft : Nat -> Char -> String -> String
--padLeft desiredLength padChar s =
--  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
--  in (List.foldl _++_ "" replicated) ++ s

concat : List String -> String
concat [] = ""
concat (str :: strs) = str <> concat strs

uncons : String -> Maybe (Pair Char String)
uncons s with unpack s
... |  [] = nothing
... |  (c :: cs) = just (c , pack cs)

head : String -> Maybe Char
head = map fst <<< uncons

tail : String -> Maybe String
tail = map snd <<< uncons

cons : Char -> String -> String
cons c s = pack (c :: unpack s)

takeWhile : (Char -> Bool) -> String -> String
takeWhile p = unpack >>> List.takeWhile p >>> pack

dropWhile : (Char -> Bool) -> String -> String
dropWhile p = unpack >>> List.dropWhile p >>> pack

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC length = toInteger . Text.length #-}
{-# COMPILE GHC startsWith = Text.isPrefixOf #-}
{-# COMPILE GHC stripPrefix = Text.stripPrefix #-}
{-# COMPILE GHC uncons = Text.uncons #-}
{-# COMPILE GHC cons = Text.cons #-}
{-# COMPILE GHC takeWhile = Text.takeWhile #-}
{-# COMPILE GHC dropWhile = Text.dropWhile #-}
