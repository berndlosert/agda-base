{-# OPTIONS --type-in-type #-}

module Data.String where

open import Agda.Builtin.String public
  using (String)
  renaming (
    primStringToList to unpack;
    primStringFromList to pack
  )

open import Data.Bool
open import Data.Char public
open import Data.Foldable
open import Data.Function
open import Data.Eq
open import Data.List
open import Data.Maybe
open import Data.Monoid
open import Data.Nat
open import Data.Pair
open import Data.Sequence

repack : (List Char -> List Char) -> String -> String
repack f = pack <<< f <<< unpack

private
  cons' : Char -> String -> String
  cons' c = repack (c ::_)

  singleton' : Char -> String
  singleton' = pack <<< singleton

  snoc' : String -> Char -> String
  snoc' s c = repack (_++ singleton c) s

  head' : String -> Maybe Char
  head' s with unpack s
  ... | [] = nothing
  ... | (c :: _) = just c

  tail' : String -> Maybe String
  tail' s with unpack s
  ... | [] = nothing
  ... | (_ :: cs) = just (pack cs)

  uncons' : String -> Maybe (Pair Char String)
  uncons' s with unpack s
  ... | [] = nothing
  ... | (c :: cs) = just (c , pack cs)

  reverse' : String -> String
  reverse' = repack reverse

  replicate' : Nat -> Char -> String
  replicate' n = pack <<< replicate n

  intersperse' : Char -> String -> String
  intersperse' = repack <<< intersperse

  takeWhile' : (Char -> Bool) -> String -> String
  takeWhile' = repack <<< takeWhile

  dropWhile' : (Char -> Bool) -> String -> String
  dropWhile' = repack <<< dropWhile

  take' : Nat -> String -> String
  take' = repack <<< take

  drop' : Nat -> String -> String
  drop' = repack <<< drop

  deleteAt' : Nat -> String -> String
  deleteAt' = repack <<< deleteAt

  modifyAt' : Nat -> (Char -> Char) -> String -> String
  modifyAt' n = repack <<< modifyAt n

  setAt' : Nat -> Char -> String -> String
  setAt' n = repack <<< setAt n

  insertAt' : Nat -> Char -> String -> String
  insertAt' n = repack <<< insertAt n

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC cons' = Text.cons #-}
{-# COMPILE GHC singleton' = Text.singleton #-}
{-# COMPILE GHC snoc' = Text.snoc #-}
--{-# COMPILE GHC head' = Text.head #-}
--{-# COMPILE GHC tail' = Text.tail #-}
--{-# COMPILE GHC uncons' = Text.uncons #-}
{-# COMPILE GHC reverse' = Text.reverse #-}
{-# COMPILE GHC replicate' = \ n c -> Text.replicate (toInteger n) (Text.singleton c) #-}
{-# COMPILE GHC intersperse' = Text.intersperse #-}
{-# COMPILE GHC takeWhile' = Text.takeWhile #-}
{-# COMPILE GHC dropWhile' = Text.dropWhile #-}
--{-# COMPILE GHC take' = Text.take #-}
--{-# COMPILE GHC drop' = Text.drop #-}
--{-# COMPILE GHC length = toInteger . Text.length #-}
--{-# COMPILE GHC startsWith = Text.isPrefixOf #-}
--{-# COMPILE GHC stripPrefix = Text.stripPrefix #-}

instance
  eqString : Eq String
  eqString ._==_ = Agda.Builtin.String.primStringEquality

  semigroupString : Semigroup String
  semigroupString ._<>_ = Agda.Builtin.String.primStringAppend

  monoidString : Monoid String
  monoidString .mempty = ""

  foldStringChar : Fold String Char
  foldStringChar .foldMap f = foldMap f <<< unpack

  sequenceStringChar : Sequence String Char
  sequenceStringChar .nil = ""
  sequenceStringChar .cons = cons'
  sequenceStringChar .singleton = singleton'
  sequenceStringChar ._++_ = Agda.Builtin.String.primStringAppend
  sequenceStringChar .snoc = snoc'
  sequenceStringChar .head = head'
  sequenceStringChar .tail = tail'
  sequenceStringChar .uncons = uncons'
  sequenceStringChar .reverse = reverse'
  sequenceStringChar .replicate = replicate'
  sequenceStringChar .intersperse = intersperse'
  sequenceStringChar .takeWhile = takeWhile'
  sequenceStringChar .dropWhile = dropWhile'
  sequenceStringChar .take = take'
  sequenceStringChar .drop = drop'
  sequenceStringChar .deleteAt = deleteAt'
  sequenceStringChar .modifyAt = modifyAt'
  sequenceStringChar .setAt = setAt'
  sequenceStringChar .insertAt = insertAt'

  --padRight : Nat -> Char -> String -> String
  --padRight desiredLength padChar s =
  --  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
  --  in s ++ (List.foldl _++_ "" replicated)
  --
  --padLeft : Nat -> Char -> String -> String
  --padLeft desiredLength padChar s =
  --  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
  --  in (List.foldl _++_ "" replicated) ++ s
