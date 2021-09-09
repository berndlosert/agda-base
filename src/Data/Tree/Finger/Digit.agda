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
  One : a -> Digit a
  Two : a -> a -> Digit a
  Three : a -> a -> a -> Digit a
  Four : a -> a -> a -> a -> Digit a

instance
  Foldable-Digit : Foldable Digit
  Foldable-Digit .foldr f z = \ where
    (One a) -> f a z
    (Two a b) -> f a (f b z)
    (Three a b c) -> f a (f b (f c z))
    (Four a b c d) -> f a (f b (f c (f d z)))

  Functor-Digit : Functor Digit
  Functor-Digit .map f = \ where
    (One a) -> One (f a)
    (Two a b) -> Two (f a) (f b)
    (Three a b c) -> Three (f a) (f b) (f c)
    (Four a b c d) -> Four (f a) (f b) (f c) (f d)

  Traversable-Digit : Traversable Digit
  Traversable-Digit .traverse f = \ where
    (One a) -> (| One (f a) |)
    (Two a b) -> (| Two (f a) (f b) |)
    (Three a b c) -> (| Three (f a) (f b) (f c) |)
    (Four a b c d) -> (| Four (f a) (f b) (f c) (f d) |)

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
splitDigit _ i (One a) = Split: nothing a nothing
splitDigit p i (Two a b) =
  let
    va = i <> measure a
  in
    if p va then Split: nothing a (just (One b))
    else Split: (just (One a)) b nothing
splitDigit p i (Three a b c) =
  let
    va = i <> measure a
    vab = va <> measure b
  in
    if p va then Split: nothing a (just (Two b c))
    else if p vab then Split: (just (One a)) b (just (One c))
    else Split: (just (Two a b)) c nothing
splitDigit p i (Four a b c d) =
  let
    va = i <> measure a
    vab = va <> measure b
    vabc = vab <> measure c
  in
    if p va then Split: nothing a (just (Three b c d))
    else if p vab then Split: (just (One a)) b (just (Two c d))
    else if p vabc then Split: (just (Two a b)) c (just (One d))
    else Split: (just (Three a b c)) d nothing

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

searchDigit : {{Measured v a}}
  -> (v -> v -> Bool)
  -> v
  -> Digit a
  -> v
  -> Split (Maybe <<< Digit) a
searchDigit _ vl (One a) vr = Split: nothing a nothing
searchDigit p vl (Two a b) vr =
  let
    va = vl <> measure a
    vb = measure b <> vr
  in
    if p va vb then Split: nothing a (just (One b))
    else Split: (just (One a)) b nothing
searchDigit p vl (Three a b c) vr =
  let
    va = vl <> measure a
    vab = va <> measure b
    vc = measure c <> vr
    vbc = measure b <> vc
  in
    if p va vbc then Split: nothing a (just (Two b c))
    else if p vab vc then Split: (just (One a)) b (just (One c))
    else Split: (just (Two a b)) c nothing
searchDigit p vl (Four a b c d) vr =
  let
    va = vl <> measure a
    vd = measure d <> vr
    vab = va <> measure b
    vcd = measure c <> vd
    vabc = vab <> measure c
    vbcd = measure b <> vcd
  in
    if p va vbcd then Split: nothing a (just (Three b c d))
    else if p vab vcd then Split: (just (One a)) b (just (Two c d))
    else if p vabc vd then Split: (just (Two a b)) c (just (One d))
    else Split: (just (Three a b c)) d nothing

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

initsDigit : Digit a -> Digit (Digit a)
initsDigit (One a) = One (One a)
initsDigit (Two a b) = Two (One a) (Two a b)
initsDigit (Three a b c) = Three (One a) (Two a b) (Three a b c)
initsDigit (Four a b c d) = Four (One a) (Two a b) (Three a b c) (Four a b c d)

tailsDigit : Digit a -> Digit (Digit a)
tailsDigit (One a) = One (One a)
tailsDigit (Two a b) = Two (Two a b) (One b)
tailsDigit (Three a b c) = Three (Three a b c) (Two b c) (One c)
tailsDigit (Four a b c d) = Four (Four a b c d) (Three b c d) (Two c d) (One d)
