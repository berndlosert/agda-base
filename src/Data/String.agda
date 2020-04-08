{-# OPTIONS --type-in-type #-}

module Data.String where

module String where

  open import Agda.Builtin.String public
    using (String)
    renaming (
      primStringToList to unpack;
      primStringFromList to pack;
      primStringEquality to eq;
      primStringAppend to append;
      primShowString to show
    )

  open import Data.Char
  open import Data.List
  open import Data.Nat

  open import Prelude

  fromChar : Char -> String
  fromChar c = pack (List.singleton c)

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
  concat (str :: strs) = append str (concat strs)

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

open String public
  using (String)

open import Data.Char
open import Data.Foldable
open import Data.List

open import Prelude

instance
  eqString : Eq String
  eqString ._==_ = String.eq

  --isStringString : IsString String
  --isStringString = record {
  --    Constraint = const Unit;
  --    fromString = \ s -> s
  --  }

  semigroupString : Semigroup String
  semigroupString ._<>_ = String.append

  monoidString : Monoid String
  monoidString .mempty = ""

  foldStringChar : Fold String Char
  foldStringChar .foldMap f = foldMap f <<< String.unpack
