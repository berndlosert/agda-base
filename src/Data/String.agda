{-# OPTIONS --type-in-type #-}

module Data.String where

import Data.List as List
import Prelude

open Prelude hiding (cons; singleton; snoc)

repack : (List Char -> List Char) -> String -> String
repack f = pack ∘ f ∘ unpack

cons : Char -> String -> String
cons c = repack (c ::_)

singleton : Char -> String
singleton = pack ∘ Prelude.singleton

snoc : String -> Char -> String
snoc s c = repack (_++ Prelude.singleton c) s

head : String -> Maybe Char
head s with unpack s
... | [] = nothing
... | (c :: _) = just c

tail : String -> Maybe String
tail s with unpack s
... | [] = nothing
... | (_ :: cs) = just (pack cs)

uncons : String -> Maybe (Tuple Char String)
uncons s with unpack s
... | [] = nothing
... | (c :: cs) = just (c , pack cs)

reverse : String -> String
reverse = repack List.reverse

replicate : Int -> Char -> String
replicate n = pack ∘ List.replicate n

intersperse : Char -> String -> String
intersperse = repack ∘ List.intersperse

takeWhile : (Char -> Bool) -> String -> String
takeWhile = repack ∘ List.takeWhile

dropWhile : (Char -> Bool) -> String -> String
dropWhile = repack ∘ List.dropWhile

take : Int -> String -> String
take = repack ∘ List.take

drop : Int -> String -> String
drop = repack ∘ List.drop

deleteAt : Int -> String -> String
deleteAt = repack ∘ List.deleteAt

modifyAt : Int -> (Char -> Char) -> String -> String
modifyAt n = repack ∘ List.modifyAt n

setAt : Int -> Char -> String -> String
setAt n = repack ∘ List.setAt n

insertAt : Int -> Char -> String -> String
insertAt n = repack ∘ List.insertAt n

isPrefixOf : String -> String -> Bool
isPrefixOf s s' = List.isPrefixOf (unpack s) (unpack s')

isSuffixOf : String -> String -> Bool
isSuffixOf s s' = List.isSuffixOf (unpack s) (unpack s')

isInfixOf : String -> String -> Bool
isInfixOf s s' = List.isInfixOf (unpack s) (unpack s')

isSubsequenceOf : String -> String -> Bool
isSubsequenceOf s s' = List.isSubsequenceOf (unpack s) (unpack s')

length : String -> Int
length = List.length ∘ unpack

filter : (Char -> Bool) -> String -> String
filter = repack ∘ List.filter

partition : (Char -> Bool) -> String -> Tuple String String
partition p s = bimap pack pack (List.partition p (unpack s))

padRight : Int -> Char -> String -> String
padRight l@(pos _) c s =
  let replicated = replicate (l - length s) c
  in s ++ replicated
padRight _ _ s = s

padLeft : Int -> Char -> String -> String
padLeft l@(pos _) c s =
  let replicated = replicate (l - length s) c
  in replicated ++ s
padLeft _ c s = s

concat : List String -> String
concat = foldr _++_ ""

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC cons = Text.cons #-}
{-# COMPILE GHC singleton = Text.singleton #-}
{-# COMPILE GHC snoc = Text.snoc #-}
{-# COMPILE GHC reverse = Text.reverse #-}
{-# COMPILE GHC replicate = \ n c -> Text.replicate (fromInteger n) (Text.singleton c) #-}
{-# COMPILE GHC intersperse = Text.intersperse #-}
{-# COMPILE GHC takeWhile = Text.takeWhile #-}
{-# COMPILE GHC dropWhile = Text.dropWhile #-}
{-# COMPILE GHC take = Text.take . fromInteger #-}
{-# COMPILE GHC drop = Text.drop . fromInteger #-}
{-# COMPILE GHC isPrefixOf = Text.isPrefixOf #-}
{-# COMPILE GHC isSuffixOf = Text.isSuffixOf #-}
{-# COMPILE GHC isInfixOf = Text.isInfixOf #-}
{-# COMPILE GHC length = toInteger. Text.length #-}
{-# COMPILE GHC filter = Text.filter #-}
