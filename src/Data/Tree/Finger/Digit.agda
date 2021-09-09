{-# OPTIONS --type-in-type #-}

module Data.Tree.Finger.Digit where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Tree.Finger.Measured
open import Data.Tree.Finger.Split
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a v : Set

-------------------------------------------------------------------------------
-- Digit
-------------------------------------------------------------------------------

data Digit (a : Set) : Set where
  one : a -> Digit a
  two : a -> a -> Digit a
  three : a -> a -> a -> Digit a
  four : a -> a -> a -> a -> Digit a

instance
  Foldable-Digit : Foldable Digit
  Foldable-Digit .foldr f z = \ where
    (one a) -> f a z
    (two a b) -> f a (f b z)
    (three a b c) -> f a (f b (f c z))
    (four a b c d) -> f a (f b (f c (f d z)))

  Functor-Digit : Functor Digit
  Functor-Digit .map f = \ where
    (one a) -> one (f a)
    (two a b) -> two (f a) (f b)
    (three a b c) -> three (f a) (f b) (f c)
    (four a b c d) -> four (f a) (f b) (f c) (f d)

  Traversable-Digit : Traversable Digit
  Traversable-Digit .traverse f = \ where
    (one a) -> (| one (f a) |)
    (two a b) -> (| two (f a) (f b) |)
    (three a b c) -> (| three (f a) (f b) (f c) |)
    (four a b c d) -> (| four (f a) (f b) (f c) (f d) |)

  Measured-Digit : {{Measured v a}} -> Measured v (Digit a)
  Measured-Digit .measure = foldMap measure

-------------------------------------------------------------------------------
-- Splitting
-------------------------------------------------------------------------------

splitDigit : {{Measured v a }}
  -> (v -> Bool)
  -> v
  -> Digit a
  -> Split (Maybe <<< Digit) a
splitDigit _ i (one a) = toSplit nothing a nothing
splitDigit p i (two a b) =
  let
    va = i <> measure a
  in
    if p va then toSplit nothing a (just (one b))
    else toSplit (just (one a)) b nothing
splitDigit p i (three a b c) =
  let
    va = i <> measure a
    vab = va <> measure b
  in
    if p va then toSplit nothing a (just (two b c))
    else if p vab then toSplit (just (one a)) b (just (one c))
    else toSplit (just (two a b)) c nothing
splitDigit p i (four a b c d) =
  let
    va = i <> measure a
    vab = va <> measure b
    vabc = vab <> measure c
  in
    if p va then toSplit nothing a (just (three b c d))
    else if p vab then toSplit (just (one a)) b (just (two c d))
    else if p vabc then toSplit (just (two a b)) c (just (one d))
    else toSplit (just (three a b c)) d nothing

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

searchDigit : {{Measured v a}}
  -> (v -> v -> Bool)
  -> v
  -> Digit a
  -> v
  -> Split (Maybe <<< Digit) a
searchDigit _ vl (one a) vr = toSplit nothing a nothing
searchDigit p vl (two a b) vr =
  let
    va = vl <> measure a
    vb = measure b <> vr
  in
    if p va vb then toSplit nothing a (just (one b))
    else toSplit (just (one a)) b nothing
searchDigit p vl (three a b c) vr =
  let
    va = vl <> measure a
    vab = va <> measure b
    vc = measure c <> vr
    vbc = measure b <> vc
  in
    if p va vbc then toSplit nothing a (just (two b c))
    else if p vab vc then toSplit (just (one a)) b (just (one c))
    else toSplit (just (two a b)) c nothing
searchDigit p vl (four a b c d) vr =
  let
    va = vl <> measure a
    vd = measure d <> vr
    vab = va <> measure b
    vcd = measure c <> vd
    vabc = vab <> measure c
    vbcd = measure b <> vcd
  in
    if p va vbcd then toSplit nothing a (just (three b c d))
    else if p vab vcd then toSplit (just (one a)) b (just (two c d))
    else if p vabc vd then toSplit (just (two a b)) c (just (one d))
    else toSplit (just (three a b c)) d nothing

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

initsDigit : Digit a -> Digit (Digit a)
initsDigit (one a) = one (one a)
initsDigit (two a b) = two (one a) (two a b)
initsDigit (three a b c) = three (one a) (two a b) (three a b c)
initsDigit (four a b c d) = four (one a) (two a b) (three a b c) (four a b c d)

tailsDigit : Digit a -> Digit (Digit a)
tailsDigit (one a) = one (one a)
tailsDigit (two a b) = two (two a b) (one b)
tailsDigit (three a b c) = three (three a b c) (two b c) (one c)
tailsDigit (four a b c d) = four (four a b c d) (three b c d) (two c d) (one d)
