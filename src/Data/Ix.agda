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
  {-# TERMINATING #-}
  ixNat : Ix Nat
  ixNat .range (m , n) =
      if m == n then [ m ]
      else if m < n then m :: range (m + 1 , n)
      else (m :: range (m - 1 , n))
  ixNat .inRange (m , n) k = m <= k && k <= n
  ixNat .rangeSize (m , n) = max (m - n) (n - m) + 1
  ixNat .index (m , n) k = if inRange (m , n) k then Just (k - m) else Nothing

  {-# TERMINATING #-}
  ixInt : Ix Int
  ixInt .range (m , n) =
      if m == n then [ m ]
      else if m < n then m :: range (m + 1 , n)
      else (m :: range (m - 1 , n))
  ixInt .inRange (m , n) k = m <= k && k <= n
  ixInt .rangeSize (m , n) = fromPos (abs (m - n)) {{believeMe}}
  ixInt .index (m , n) k =
    if inRange (m , n) k
    then Just $ fromPos (abs $ k - m) {{believeMe}}
    else Nothing
