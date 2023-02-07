module Data.Either.Nary where

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
    as bs : List Set

-------------------------------------------------------------------------------
-- EitherN
-------------------------------------------------------------------------------

data EitherN (as : List Set) : Set where
  inject : Elem a as -> a -> EitherN as

instance
  Uninhabited-EitherN : Uninhabited (EitherN [])
  Uninhabited-EitherN .uninhabited _ = panic "EitherN [] is uninhabited"

project : Elem a as -> EitherN as -> Maybe a
project elem (inject elem' x) =
  if Elem.pos elem == Elem.pos elem'
    then just (unsafeCoerce x)
    else nothing

decompose : EitherN (a :: as) -> Either a (EitherN as)
decompose (inject elem x) =
  if Elem.pos elem == 0
    then left (unsafeCoerce x)
    else right $ inject (elemPos $ Elem.pos elem - 1) x

relax : Sub as bs -> EitherN as -> EitherN bs
relax nilSub x = absurd x
relax (consSub h t) x with decompose x
... | left y = inject h y
... | right z = relax t z

eitherN : (a -> b) -> (EitherN as -> b) -> EitherN (a :: as) -> b
eitherN f g x with decompose x
... | left y = f y
... | right z = g z
