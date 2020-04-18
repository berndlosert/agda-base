{-# OPTIONS --type-in-type #-}

module Data.String where

open import Agda.Builtin.String public
  renaming (
    primStringToList to unpack;
    primStringFromList to pack
  )

open import Data.Buildable
open import Data.Char
open import Data.Foldable
open import Data.Eq
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Monoid
open import Data.Semigroup
open import Data.Sequence
open import Prim

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

  partition' : (Char -> Bool) -> String -> Pair String String
  partition' p s = let (l , r) = partition p (unpack s) in
    (pack l , pack r)

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
{-# COMPILE GHC partition' = Text.partition #-}

instance
  eqString : Eq String
  eqString ._==_ = Agda.Builtin.String.primStringEquality

  semigroupString : Semigroup String
  semigroupString ._<>_ = Agda.Builtin.String.primStringAppend

  monoidString : Monoid String
  monoidString .mempty = ""

  isBuildableStringChar : IsBuildable String Char
  isBuildableStringChar .singleton = singleton'

  isFoldableStringChar : IsFoldable String Char
  isFoldableStringChar .foldMap f = foldMap f <<< unpack

  sequenceStringChar : Sequence String Char
  sequenceStringChar = \ where
    .cons -> cons'
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
    .partition -> partition'

padRight : Nat -> Char -> String -> String
padRight l c s =
  let replicated = replicate (monus l (length s)) c
  in s ++ replicated

padLeft : Nat -> Char -> String -> String
padLeft l c s =
  let replicated = replicate (monus l (length s)) c
  in replicated ++ s
