module Data.Semigroup.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.List.Nonempty
open import Data.Monoid.Dual
open import Data.Monoid.Foldable
open import Data.Monoid.Product
open import Data.Monoid.Sum
open import Data.Semigroup.First
open import Data.Semigroup.FromMaybe
open import Data.Semigroup.FromMaybeM
open import Data.Semigroup.Last
open import Data.Semigroup.Max
open import Data.Semigroup.Min
open import Data.Semigroup.Strict

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Monoid.Dual public
open Data.Monoid.Product public
open Data.Monoid.Sum public
open Data.Semigroup.FromMaybe public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    f m t : Type -> Type

-------------------------------------------------------------------------------
-- Literals
-------------------------------------------------------------------------------

instance
  _ = FromNat-Nat1

-------------------------------------------------------------------------------
-- Foldable1
-------------------------------------------------------------------------------

record Foldable1 (t : Type -> Type) : Type where
  field 
    overlap {{Foldable-super}} : Foldable t
    foldMap1 : {{Semigroup b}} -> (a -> b) -> t a -> b

  foldr1 : (a -> b -> b) -> (a -> b) -> t a -> b
  foldr1 {a} {b} step init xs = appFromMaybe (foldMap1 h xs) nothing
    where
      h : a -> FromMaybe b
      h x = asFromMaybe \ where
        (just y) -> step x y
        nothing -> init x

  foldl1 : (b -> a -> b) -> (a -> b) -> t a -> b
  foldl1 {b} {a} step init xs =
      appFromMaybe (getStrict $ getDual $ foldMap1 h xs) nothing
    where
      h : a -> Dual (Strict FromMaybe b)
      h x = asDual $ asStrict $ asFromMaybe \ where
        (just y) -> step y x
        nothing -> init x

  fold1 : {{Semigroup a}} -> t a -> a
  fold1 = foldMap1 id

  foldrM1 : {{Monad m}} -> (a -> b -> m b) -> (a -> m b) -> t a -> m b
  foldrM1 {m} {a} {b} step init xs = 
      appFromMaybeM (foldMap1 h xs) nothing
    where
      h : a -> FromMaybeM m b
      h x = asFromMaybeM \ where
        nothing -> init x
        (just y) -> step x y

  foldlM1 : {{Monad m}} -> (b -> a -> m b) -> (a -> m b) -> t a -> m b
  foldlM1 {m} {b} {a} step init xs = 
      appFromMaybeM (getDual $ foldMap1 h xs) nothing
    where
      h : a -> Dual (FromMaybeM m b)
      h x = asDual $ asFromMaybeM \ where
        nothing -> init x
        (just y) -> step y x

  toList1 : t a -> List1 a
  toList1 = foldMap1 (_:: [])
  
  concat1 : t (List1 a) -> List1 a
  concat1 = fold1

  concatMap1 : (a -> List1 b) -> t a -> List1 b
  concatMap1 = foldMap1

  length1 : t a -> Nat1
  length1 = foldl1 inc (const 1)
    where
      inc : Nat1 -> a -> Nat1
      inc n _ = suc (toNat n)

  first : t a -> a
  first = getFirst <<< foldMap1 asFirst

  last : t a -> a
  last = getLast <<< foldMap1 asLast

  sum1 : {{Semigroup (Sum a)}} -> t a -> a
  sum1 {a} = getSum <<< foldl1 step asSum
    where
      step : Sum a -> a -> Sum a
      step x y = x <> asSum y

  product1 : {{Semigroup (Product a)}} -> t a -> a
  product1 {a} = getProduct <<< foldl1 step asProduct
    where
      step : Product a -> a -> Product a
      step x y = x <> asProduct y

  minimum : {{Ord a}} -> t a -> a
  minimum {a} = getMin <<< foldl1 step asMin
    where
      step : Min a -> a -> Min a
      step x y = x <> asMin y

  maximum : {{Ord a}} -> t a -> a
  maximum {a} = getMax <<< foldl1 step asMax
    where
      step : Max a -> a -> Max a
      step x y = x <> asMax y

  minimumBy : (a -> a -> Ordering) -> t a -> a
  minimumBy cmp = let instance _ = order cmp in minimum

  maximumBy : (a -> a -> Ordering) -> t a -> a
  maximumBy cmp = let instance _ = order cmp in maximum

open Foldable1 {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable1-Identity : Foldable1 Identity
  Foldable1-Identity .foldMap1 f x = f (runIdentity x)

  Foldable1-List1 : Foldable1 List1
  Foldable1-List1 .foldMap1 f = \ where
    (x :: []) -> f x
    (x :: (y :: ys)) -> f x <> foldMap1 f (y :: ys)
