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

  isPrefixOf' : String -> String -> Bool
  isPrefixOf' s s' = isPrefixOf {{eq = eqChar}} (unpack s) (unpack s')

  isSuffixOf' : String -> String -> Bool
  isSuffixOf' s s' = isSuffixOf {{eq = eqChar}} (unpack s) (unpack s')

  isInfixOf' : String -> String -> Bool
  isInfixOf' s s' = isInfixOf {{eq = eqChar}} (unpack s) (unpack s')

  isSubsequenceOf' : String -> String -> Bool
  isSubsequenceOf' s s' = isSubsequenceOf {{eq = eqChar}} (unpack s) (unpack s')

  null' : String -> Bool
  null' = null <<< unpack

  length' : String -> Nat
  length' = length <<< unpack

  filter' : (Char -> Bool) -> String -> String
  filter' = repack <<< filter

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC cons' = Text.cons #-}
{-# COMPILE GHC singleton' = Text.singleton #-}
{-# COMPILE GHC snoc' = Text.snoc #-}
{-# COMPILE GHC reverse' = Text.reverse #-}
{-# COMPILE GHC replicate' = \ n c -> Text.replicate (fromInteger n) (Text.singleton c) #-}
{-# COMPILE GHC intersperse' = Text.intersperse #-}
{-# COMPILE GHC takeWhile' = Text.takeWhile #-}
{-# COMPILE GHC dropWhile' = Text.dropWhile #-}
{-# COMPILE GHC take' = Text.take . fromInteger #-}
{-# COMPILE GHC drop' = Text.drop . fromInteger #-}
{-# COMPILE GHC isPrefixOf' = Text.isPrefixOf #-}
{-# COMPILE GHC isSuffixOf' = Text.isSuffixOf #-}
{-# COMPILE GHC isInfixOf' = Text.isInfixOf #-}
{-# COMPILE GHC null' = Text.null #-}
{-# COMPILE GHC length' = toInteger. Text.length #-}
{-# COMPILE GHC filter' = Text.filter #-}

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
  sequenceStringChar = \ where
    .nil -> ""
    .cons -> cons'
    .singleton -> singleton'
    ._++_ -> Agda.Builtin.String.primStringAppend
    .snoc -> snoc'
    .head -> head'
    .tail -> tail'
    .uncons -> uncons'
    .reverse -> reverse'
    .replicate -> replicate'
    .intersperse -> intersperse'
    .takeWhile -> takeWhile'
    .dropWhile -> dropWhile'
    .take -> take'
    .drop -> drop'
    .deleteAt -> deleteAt'
    .modifyAt -> modifyAt'
    .setAt -> setAt'
    .insertAt -> insertAt'
    .isPrefixOf -> isPrefixOf'
    .isSuffixOf -> isSuffixOf'
    .isInfixOf -> isInfixOf'
    .isSubsequenceOf -> isSubsequenceOf'
    .null -> null'
    .length -> length'
    .filter -> filter'

  --padRight : Nat -> Char -> String -> String
  --padRight desiredLength padChar s =
  --  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
  --  in s ++ (List.foldl _++_ "" replicated)
  --
  --padLeft : Nat -> Char -> String -> String
  --padLeft desiredLength padChar s =
  --  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
  --  in (List.foldl _++_ "" replicated) ++ s
