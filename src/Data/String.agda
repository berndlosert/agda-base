{-# OPTIONS --type-in-type #-}

module Data.String where

import Data.List as List
import Prelude

open Prelude

fromChar : Char -> String
fromChar c = pack (pure c)

length : String -> Nat
length = unpack >>> List.length

startsWith : String -> String -> Bool
startsWith s s' = List.isPrefixOf (unpack s) (unpack s')

stripPrefix : String -> String -> Maybe String
stripPrefix s s' = pack <$> List.stripPrefix (unpack s) (unpack s')

padRight : Nat -> Char -> String -> String
padRight desiredLength padChar s =
  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
  in s ++ (List.foldl _++_ "" replicated)

padLeft : Nat -> Char -> String -> String
padLeft desiredLength padChar s =
  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
  in (List.foldl _++_ "" replicated) ++ s

concat : List String -> String
concat [] = ""
concat (str :: strs) = str ++ concat strs

uncons : String -> Maybe (Char * String)
uncons s with unpack s
... |  [] = nothing
... |  (c :: cs) = just (Pair: c (pack cs))

head : String -> Maybe Char
head = map fst <<< uncons

tail : String -> Maybe String
tail = map snd <<< uncons

cons : Char -> String -> String
cons c s = pack (c :: unpack s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC length = toInteger . Text.length #-}
{-# COMPILE GHC startsWith = Text.isPrefixOf #-}
{-# COMPILE GHC stripPrefix = Text.stripPrefix #-}
{-# COMPILE GHC uncons = Text.uncons #-}
{-# COMPILE GHC cons = Text.cons #-}
