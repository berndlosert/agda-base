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
  IxNat : Ix Nat
  IxNat .range (m , n) =
      if m == n then [ m ]
      else if m < n then m :: range (m + 1 , n)
      else (m :: range (m - 1 , n))
  IxNat .inRange (m , n) k = m <= k && k <= n
  IxNat .rangeSize (m , n) = max (m - n) (n - m) + 1
  IxNat .index (m , n) k = if inRange (m , n) k then Just (k - m) else Nothing

  IxInt : Ix Int
  IxInt .range (m , n) =
      if m == n then [ m ]
      else if m < n then m :: range (m + 1 , n)
      else (m :: range (m - 1 , n))
  IxInt .inRange (m , n) k = m <= k && k <= n
  IxInt .rangeSize (m , n) = fromPos (abs (m - n)) {{believeMe}}
  IxInt .index (m , n) k =
    if inRange (m , n) k
    then Just $ fromPos (abs $ k - m) {{believeMe}}
    else Nothing
