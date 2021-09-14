{-# OPTIONS --type-in-type #-}

module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.String
open import Constraint.NonEmpty
open import Control.Monad.Free.General
open import Data.Char as Char using ()
open import Data.List as List using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Creation and elimination
-------------------------------------------------------------------------------

pack : List Char -> String
pack = primStringFromList

unpack : String -> List Char
unpack = primStringToList

singleton : Char -> String
singleton = pack <<< List.singleton

empty : String
empty = ""

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC singleton = Text.singleton #-}

-------------------------------------------------------------------------------
-- Basic interface
-------------------------------------------------------------------------------

cons : Char -> String -> String
cons c s = singleton c <> s

snoc : String -> Char -> String
snoc s c = s <> singleton c

append : String -> String -> String
append = _<>_

uncons : (s : String) -> {{Assert $ nonempty s}} -> Pair Char String
uncons "" = error "Data.String.uncons: bad argument"
uncons s = case primStringUncons s of \ where
  (just p) -> fst p , snd p
  nothing -> error "Data.String.uncons: bad argument"

unsnoc : (s : String) -> {{Assert $ nonempty s}} -> Pair String Char
unsnoc "" = error "Data.String.unsnoc: bad argument"
unsnoc s = lmap pack $ List.unsnoc (unpack s) {{trustMe}}

head : (s : String) -> {{Assert $ nonempty s}} -> Char
head "" = error "Data.String.head: bad argument"
head s = fst (uncons s)

tail : (s : String) -> {{Assert $ nonempty s}} -> String
tail "" = error "Data.String.tail: bad argument"
tail s = snd (uncons s)

length : String -> Nat
length = List.length <<< unpack

init : (s : String) -> {{Assert $ nonempty s}} -> String
init "" = error "Data.String.init: bad argument"
init s = pack $ List.init (unpack s) {{trustMe}}

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC cons = Text.cons #-}
{-# COMPILE GHC snoc = Text.snoc #-}
{-# COMPILE GHC uncons = Text.uncons #-}
{-# COMPILE GHC unsnoc = Text.unsnoc #-}
{-# COMPILE GHC length = toInteger . Text.length #-}

-------------------------------------------------------------------------------
-- Generation and unfolding
-------------------------------------------------------------------------------

replicate : Nat -> String -> String
replicate n s = List.fold (List.replicate n s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC replicate = Text.replicate . fromInteger #-}

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : String -> String
reverse s = pack $ List.reverse $ unpack s

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC reverse = Text.reverse #-}

-------------------------------------------------------------------------------
-- Justification
-------------------------------------------------------------------------------

justifyLeft : Nat -> Char -> String -> String
justifyLeft l c s = s <> replicate (l - length s) (singleton c)

justifyRight : Nat -> Char -> String -> String
justifyRight l c s = replicate (l - length s) (singleton c) <> s

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC justifyLeft = Text.justifyLeft . fromInteger #-}
{-# COMPILE GHC justifyRight = Text.justifyRight . fromInteger #-}

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

foldl : (a -> Char -> a) -> a -> String -> a
foldl f z s = List.foldl f z (unpack s)

-------------------------------------------------------------------------------
-- Breaking strings
-------------------------------------------------------------------------------

take : Nat -> String -> String
take n s = pack $ List.take n $ unpack s

takeWhile : (Char -> Bool) -> String -> String
takeWhile p s = pack $ List.takeWhile p $ unpack s

drop : Nat -> String -> String
drop n s = pack $ List.drop n $ unpack s

dropWhile : (Char -> Bool) -> String -> String
dropWhile p s = pack $ List.dropWhile p $ unpack s

span : (Char -> Bool) -> String -> Pair String String
span p s = bimap pack pack $ List.span p $ unpack s

break : (Char -> Bool) -> String -> Pair String String
break p s = bimap pack pack $ List.break p $ unpack s

breakOn : String -> String -> Pair String String
breakOn delim s = bimap pack pack $ List.breakOn (unpack delim) (unpack s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC take = Text.take . fromInteger #-}
{-# COMPILE GHC takeWhile = Text.takeWhile #-}
{-# COMPILE GHC drop = Text.drop . fromInteger #-}
{-# COMPILE GHC dropWhile = Text.dropWhile #-}
{-# COMPILE GHC span = Text.span #-}
{-# COMPILE GHC break = Text.break #-}
{-# COMPILE GHC breakOn = Text.breakOn #-}

-------------------------------------------------------------------------------
-- Breaking into many substrings
-------------------------------------------------------------------------------

splitOn : String -> String -> List String
splitOn delim s = map pack $ List.splitOn (unpack delim) (unpack s)

split : (Char -> Bool) -> String -> List String
split f s = map pack $ List.split f (unpack s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC split = Text.split #-}

-------------------------------------------------------------------------------
-- Breaking into lines and words
-------------------------------------------------------------------------------

words : String -> List String
words = combust go
  where
    go  : Fn String (List String)
    go s = do
      let s' = dropWhile Char.isSpace s
      case s' == "" of \ where
        true -> pure []
        false -> do
          let (w , s'') = break Char.isSpace s'
          ws <- call s''
          pure $ w :: ws

unwords : List String -> String
unwords [] = ""
unwords (w :: ws) = w <> go ws
  where
    go : List String -> String
    go [] = ""
    go (v :: vs) = " " <> v <> go vs

lines : String -> List String
lines s =
    let (l , ls) = foldl go ("" , []) s
    in List.reverse (if l == "" then ls else (l :: ls))
  where
    go : Pair String (List String) -> Char -> Pair String (List String)
    go (l , ls) '\n' = ("" , l :: ls)
    go (l , ls) c = (snoc l c , ls)

unlines : List String -> String
unlines = List.fold <<< map (_<> "\n")

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC words = Text.words #-}
{-# COMPILE GHC unwords = Text.unwords #-}
{-# COMPILE GHC lines = Text.lines #-}
{-# COMPILE GHC unlines = Text.unlines #-}

-------------------------------------------------------------------------------
-- View
-------------------------------------------------------------------------------

data AsList : String -> Set where
  [] : AsList ""
  _::_ : (c : Char) {s : String} -> AsList s -> AsList (cons c s)

cons-uncons : (s : String) {{_ : Assert $ nonempty s}}
  -> (uncurry cons) (uncons s) === s
cons-uncons = trustMe

{-# TERMINATING #-}
asList : (s : String) -> AsList s
asList "" = []
asList s with uncons s {{trustMe}} | cons-uncons s {{trustMe}}
... | c , s' | refl = c :: asList s'
