module Data.Union where

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
    as : List Set

-------------------------------------------------------------------------------
-- Union
-------------------------------------------------------------------------------

private
  data Union' (as : List Set) : Set where
    unsafeInject : Nat -> a -> Union' as

  unsafeProject : (a : Set) -> Union' as -> Nat -> Maybe a
  unsafeProject _ (unsafeInject n x) n' =
    if n == n' then just (unsafeCoerce x) else nothing

Union = Union'

instance
  Uninhabited-Union : Uninhabited (Union [])
  Uninhabited-Union .uninhabited _ = panic "Union [] is uninhabited"

inject : {{Elem a as}} -> a -> Union as
inject {{prf}} x = unsafeInject (elemPos {{prf}}) x

project : {{Elem a as}} -> Union as -> Maybe a
project {{prf}} u = unsafeProject _ u (elemPos {{prf}})

union : (a -> b) -> (Union as -> b) -> Union (a :: as) -> b
union f g (unsafeInject 0 x) = f (unsafeCoerce x)
union f g (unsafeInject (suc n) x) = g (unsafeInject n x)