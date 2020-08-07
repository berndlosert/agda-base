module Data.Ix where

open import Prelude

record Ix (a : Set) : Set where
  field
    range : a * a -> List a
    inRange : a * a -> a -> Bool
    rangeSize : a * a -> Nat
    index : a * a -> a -> Maybe Nat

open Ix {{...}} public

instance
  Ix-Nat : Ix Nat
  Ix-Nat .range (m , n) =
      if m == n then [ m ]
      else if m < n then m :: range (m + 1 , n)
      else (m :: range (m - 1 , n))
  Ix-Nat .inRange (m , n) k = m <= k && k <= n
  Ix-Nat .rangeSize (m , n) = max (m - n) (n - m) + 1
  Ix-Nat .index (m , n) k = if inRange (m , n) k then Just (k - m) else Nothing

  Ix-Int : Ix Int
  Ix-Int .range (m , n) =
      if m == n then [ m ]
      else if m < n then m :: range (m + 1 , n)
      else (m :: range (m - 1 , n))
  Ix-Int .inRange (m , n) k = m <= k && k <= n
  Ix-Int .rangeSize (m , n) = fromPos (abs (m - n)) {{believeMe}}
  Ix-Int .index (m , n) k =
    if inRange (m , n) k
    then Just $ fromPos (abs $ k - m) {{believeMe}}
    else Nothing
