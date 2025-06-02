module Data.Enum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Nat.Fin

-------------------------------------------------------------------------------
-- Literals
-------------------------------------------------------------------------------

instance
  _ = FromNat-Int

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

record Enum (a : Type) : Type where
  field
    overlap {{Ord-super}} : Ord a
    enumFromTo : a -> a -> List a

open Enum {{...}} public

instance
  Enum-Fin : forall {n} {{_ : Assert (n > 0)}} -> Enum (Fin n)
  Enum-Fin .enumFromTo k m =
    case (compare k m) \ where
      equal -> k :: []
      less -> k :: enumFromTo (k + 1) m
      greater -> k :: enumFromTo (k - 1) m

  Enum-Nat : Enum Nat
  Enum-Nat .enumFromTo m n =
    case (compare m n) \ where
      equal -> m :: []
      less -> m :: enumFromTo (m + 1) n
      greater -> m :: enumFromTo (n - 1) n

  Enum-Nat1 : Enum Nat1
  Enum-Nat1 .enumFromTo (suc m) (suc n) =
    map suc (enumFromTo m n)

  Enum-Int : Enum Int
  Enum-Int .enumFromTo i j =
    case (compare i j) \ where
      equal -> i :: []
      less -> i :: enumFromTo (i + 1) j
      greater -> i :: enumFromTo (i - 1) j
