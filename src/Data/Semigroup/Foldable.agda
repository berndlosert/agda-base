module Data.Semigroup.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.List.Nonempty
open import Data.Monoid.Dual
open import Data.Monoid.Foldable
open import Data.Monoid.Product
open import Data.Monoid.Strict
open import Data.Monoid.Sum
open import Data.Semigroup.First
open import Data.Semigroup.FromMaybe
open import Data.Semigroup.Last
open import Data.Semigroup.Max
open import Data.Semigroup.Min

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
  foldr1 {a} {b} step gen xs = 
      appFromMaybe (foldMap1 step' xs) nothing
    where
      step' : a -> FromMaybe b
      step' x = asFromMaybe \ where
        (just y) -> step x y
        nothing -> gen x

  foldl1 : (b -> a -> b) -> (a -> b) -> t a -> b
  foldl1 {b} {a} step gen xs =
      appFromMaybe (getStrict $ getDual $ foldMap1 step' xs) nothing
    where
      step' : a -> Dual (Strict FromMaybe b)
      step' x = asDual $ asStrict $ asFromMaybe \ where
        (just y) -> step y x
        nothing -> gen x

  fold1 : {{Semigroup a}} -> t a -> a
  fold1 = foldMap1 id

  foldrM1 : {{Monad m}} -> (a -> b -> m b) -> (a -> m b) -> t a -> m b
  foldrM1 {m} {a} {b} step init xs = foldMap1 {{semigroup}} step' xs nothing
    where
      semigroup : Semigroup (Maybe b -> m b)
      semigroup ._<>_ g f x = g =<< just <$> f x

      step' : a -> Maybe b -> m b
      step' x nothing = init x
      step' x (just y) = step x y

  foldlM1 : {{Monad m}} -> (b -> a -> m b) -> (a -> m b) -> t a -> m b
  foldlM1 {m} {b} {a} step init xs = foldMap1 {{semigroup}} step' xs nothing
    where
      semigroup : Semigroup (Maybe b -> m b)
      semigroup ._<>_ g f x = f =<< just <$> g x

      step' : a -> Maybe b -> m b
      step' x nothing = init x
      step' x (just y) = step y x

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
  sum1 {a} = getSum <<< foldl1 (\ x y -> x <> asSum y) asSum

  product1 : {{Semigroup (Product a)}} -> t a -> a
  product1 = getProduct <<< foldl1 (\ x y -> x <> asProduct y) asProduct

  minimum : {{Ord a}} -> t a -> a
  minimum = getMin <<< foldl1 (\ x y -> x <> asMin y) asMin

  maximum : {{Ord a}} -> t a -> a
  maximum = getMax <<< foldl1 (\ x y -> x <> asMax y) asMax

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
