module Data.Functor.Sum.Nary where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.List.Elem

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    f g : Set -> Set
    fs gs : List (Set -> Set)

-------------------------------------------------------------------------------
-- SumN
-------------------------------------------------------------------------------

data SumN (fs : List (Set -> Set)) (a : Set): Set where
  inject : Elem f fs -> f a -> SumN fs a

instance
  Uninhabited-SumN : Uninhabited (SumN [] a)
  Uninhabited-SumN .uninhabited _ = panic "SumN [] a is uninhabited"

project : Elem f fs -> SumN fs a -> Maybe (f a)
project elem (inject elem' x) =
  if Elem.pos elem == Elem.pos elem'
    then just (unsafeCoerce x)
    else nothing

decompose : SumN (f :: fs) a -> Either (f a) (SumN fs a)
decompose sum@(inject {f'} elem x) with project elem sum
... | just x = left (unsafeCoerce x)
... | nothing =
  let
    elem' : Elem f' _
    elem' = elemPos (Elem.pos elem - 1)
  in
    right (inject elem' x)

relax : Sub fs gs -> SumN fs a -> SumN gs a
relax nilSub x = absurd x
relax (consSub h t) x with decompose x
... | left y = inject h y
... | right z = relax t z

sumN : (f a -> b) -> (SumN fs a -> b) -> SumN (f :: fs) a -> b
sumN f g x with decompose x
... | left y = f y
... | right z = g z
