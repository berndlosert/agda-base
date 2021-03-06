{-# OPTIONS --type-in-type #-}

module Data.Tree.Finger.Digit where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Tree.Finger.Measured
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a v : Type

-------------------------------------------------------------------------------
-- Digit
-------------------------------------------------------------------------------

data Digit (a : Type) : Type where
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

  Measured-Digit : {{_ : Measured v a}} -> Measured v (Digit a)
  Measured-Digit .measure = foldMap measure

-------------------------------------------------------------------------------
-- Splitting
-------------------------------------------------------------------------------

splitDigit : {{_ : Measured v a }}
  -> (v -> Bool)
  -> v
  -> Digit a
  -> Maybe (Digit a) * a * Maybe (Digit a)
splitDigit _ i (One a) = (Nothing , a , Nothing)
splitDigit p i (Two a b) =
  let
    va = i <> measure a
  in
    if p va then (Nothing , a , Just (One b))
    else (Just (One a) , b , Nothing)
splitDigit p i (Three a b c) =
  let
    va = i <> measure a
    vab = va <> measure b
  in
    if p va then (Nothing , a , Just (Two b c))
    else if p vab then (Just (One a) , b , Just (One c))
    else (Just (Two a b) , c , Nothing)
splitDigit p i (Four a b c d) =
  let
    va = i <> measure a
    vab = va <> measure b
    vabc = vab <> measure c
  in
    if p va then (Nothing , a , Just (Three b c d))
    else if p vab then (Just (One a) , b , Just (Two c d))
    else if p vabc then (Just (Two a b) , c , Just (One d))
    else (Just (Three a b c) , d , Nothing)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

searchDigit : {{_ : Measured v a}}
  -> (v -> v -> Bool)
  -> v
  -> Digit a
  -> v
  -> Maybe (Digit a) * a * Maybe (Digit a)
searchDigit _ vl (One a) vr = (Nothing , a , Nothing)
searchDigit p vl (Two a b) vr =
  let
    va = vl <> measure a
    vb = measure b <> vr
  in
    if p va vb then (Nothing , a , Just (One b))
    else (Just (One a) , b , Nothing)
searchDigit p vl (Three a b c) vr =
  let
    va = vl <> measure a
    vab = va <> measure b
    vc = measure c <> vr
    vbc = measure b <> vc
  in
    if p va vbc then (Nothing , a , Just (Two b c))
    else if p vab vc then (Just (One a) , b , Just (One c))
    else (Just (Two a b) , c , Nothing)
searchDigit p vl (Four a b c d) vr =
  let
    va = vl <> measure a
    vd = measure d <> vr
    vab = va <> measure b
    vcd = measure c <> vd
    vabc = vab <> measure c
    vbcd = measure b <> vcd
  in
    if p va vbcd then (Nothing , a , Just (Three b c d))
    else if p vab vcd then (Just (One a) , b , Just (Two c d))
    else if p vabc vd then (Just (Two a b) , c , Just (One d))
    else (Just (Three a b c) , d , Nothing)

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
