module Data.String where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.String
open import Data.Char as Char using ()
open import Data.List as List using ()
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

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

uncons : String -> Maybe (Tuple Char String)
uncons s = case (primStringUncons s) \ where
  (just p) -> just (fst p , snd p)
  nothing -> nothing

unsnoc : String -> Maybe (Tuple String Char)
unsnoc s = case (List.unsnoc (unpack s)) \ where
  nothing -> nothing
  (just (cs , c)) -> just (pack cs , c)

head : String -> Maybe Char
head s = fst <$> uncons s

tail : String -> Maybe String
tail s = snd <$> uncons s

length : String -> Nat
length = List.length <<< unpack

init : String -> Maybe String
init s = pack <$> List.init (unpack s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC cons = Text.cons #-}
{-# COMPILE GHC snoc = Text.snoc #-}
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
take n s = pack (List.take n (unpack s))

takeWhile : (Char -> Bool) -> String -> String
takeWhile p s = pack (List.takeWhile p (unpack s))

drop : Nat -> String -> String
drop n s = pack (List.drop n (unpack s))

dropWhile : (Char -> Bool) -> String -> String
dropWhile p s = pack (List.dropWhile p (unpack s))

span : (Char -> Bool) -> String -> Tuple String String
span p s = case (List.span p (unpack s)) \ where
  (cs , ds) -> (pack cs , pack ds)

break : (Char -> Bool) -> String -> Tuple String String
break p s = case (List.break p (unpack s)) \ where
  (cs , ds) -> (pack cs , pack ds)

breakOn : String -> String -> Tuple String String
breakOn delim s = case (List.breakOn (unpack delim) (unpack s)) \ where
  (cs , ds) -> (pack cs , pack ds)

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
splitOn delim s = pack <$> List.splitOn (unpack delim) (unpack s)

split : (Char -> Bool) -> String -> List String
split f s = pack <$> List.split f (unpack s)

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC split = Text.split #-}

-------------------------------------------------------------------------------
-- Breaking into lines and words
-------------------------------------------------------------------------------

words : String -> List String
words s =
  let s1 = dropWhile Char.isSpace s
  in case (s1 == "") \ where
    true -> []
    false ->
      let (w , s2) = break Char.isSpace s1
      in w :: words s2

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
    go : Tuple String (List String) -> Char -> Tuple String (List String)
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

data AsList : String -> Type where
  [] : AsList ""
  _::_ : (c : Char) {s : String} -> AsList s -> AsList (cons c s)

prop-uncons : (s : String) ->
  case (uncons s) \ where
    nothing -> s === ""
    (just (c , s1)) -> s === cons c s1
prop-uncons = trustMe

asList : (s : String) -> AsList s
asList s with uncons s | prop-uncons s
... | nothing | refl = []
... | just (c , s1) | refl = c :: asList s1
