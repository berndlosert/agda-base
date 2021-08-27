{-# OPTIONS --type-in-type #-}

module Data.Enum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Int as Int using ()

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

record Enum (a : Type) : Type where
  field
    {{Ord-super}} : Ord a
    suc : a -> Maybe a
    pred : a -> Maybe a
    enumFromTo : a -> a -> List a

open Enum {{...}} public

instance
  Enum-Nat : Enum Nat
  Enum-Nat .suc x = Just (Suc x)
  Enum-Nat .pred 0 = Nothing
  Enum-Nat .pred (Suc n) = Just n
  Enum-Nat .enumFromTo m n =
      let k = max (m - n) (n - m)
      in go k m n
    where
      go : Nat -> Nat -> Nat -> List Nat
      go 0 m _ = m :: []
      go (Suc k) m n =
        let m' = if m < n then m + 1 else m - 1
        in m :: go k m' n

  Enum-Int : Enum Int
  Enum-Int .suc (Pos n) = Just $ Pos (Suc n)
  Enum-Int .suc (NegSuc n) = Just $ Int.neg n
  Enum-Int .pred (Pos 0) = Just $ NegSuc 0
  Enum-Int .pred (Pos (Suc n)) = Just $ Pos n
  Enum-Int .pred (NegSuc n) = Just $ NegSuc (Suc n)
  Enum-Int .enumFromTo m n =
    case m - n of \ where
      (Pos k) -> (\ i -> Pos i + n) <$> enumFromTo k 0
      (NegSuc k) -> (\ i -> Pos i + m) <$> enumFromTo 0 (Suc k)

  --Enum-Char : Enum Char
  --Enum-Char .suc c =
  --  if c == maxChar
  --    then Nothing
  --    else fromNat <$> suc (ord c)
  --Enum-Char .pred c =
  --  if c == minChar
  --    then Nothing
  --    else natToChar <$> pred (ord c)
  --Enum-Char .enumFromTo c d = fromNat <$> enumFromTo (ord c) (ord d)
