module Data.Semigroup.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.Sum
open import Data.Monoid.Product
open import Data.Semigroup.FromMaybe
open import Data.Semigroup.Last
open import Data.Semigroup.First
open import Data.Semigroup.Max
open import Data.Semigroup.Min
open import Data.Monoid.Foldable

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
  field foldMap1 : {{Semigroup b}} -> (a -> b) -> t a -> b

  toList1 : t a -> List1 a
  toList1 = foldMap1 (_:: [])

  foldr1 : (a -> Maybe b -> b) -> t a -> b
  foldr1 step xs = appFromMaybe (foldMap1 (asFromMaybe <<< step) xs) nothing

  foldrMap1 : (a -> b -> b) -> (a -> b) -> t a -> b
  foldrMap1 step f = foldr1 \ where
    x nothing -> f x
    x (just y) -> step x y

  foldl1 : (Maybe b -> a -> b) -> t a -> b
  foldl1 {b} {a} step xs = foldr1 g xs nothing
    where
      g : a -> Maybe (Maybe b -> b) -> Maybe b -> b
      g x (just k) nothing = k (just $! step nothing x)
      g x (just k) (just y) = k (just $! step (just $! y) x)
      g x nothing nothing = id $! step nothing x
      g x nothing (just y) = id $! step (just $! y) x

  fold1 : {{Semigroup a}} -> t a -> a
  fold1 = foldMap1 id

  foldlMapM1 : {{Monad m}} -> (b -> a -> m b) -> (a -> m b) -> t a -> m b
  foldlMapM1 step f xs =
    case (toList1 xs) \ where
      (x :: xs) -> f x >>= \ y -> foldlM step y xs

  foldlM1 : {{Monad m}} -> (Maybe b -> a -> m b) -> t a -> m b
  foldlM1 step = foldlMapM1 (\ y x -> step (just y) x) (\ x -> step nothing x)

  foldrMapM1 : {{Monad m}} -> (a -> b -> m b) -> (a -> m b) -> t a -> m b
  foldrMapM1 {m} {a} {b} step f = go <<< toList1
    where
      go : List1 a -> m b
      go (x :: []) = f x
      go (x :: y :: ys) = go (y :: ys) >>= step x

  foldrM1 : {{Monad m}} -> (a -> Maybe b -> m b) -> t a -> m b
  foldrM1 step = foldrMapM1 (\ x y -> step x (just y)) (\ x -> step x nothing)

  concat1 : t (List1 a) -> List1 a
  concat1 = fold1

  concatMap1 : (a -> List1 b) -> t a -> List1 b
  concatMap1 = foldMap1

  length1 : t a -> Nat1
  length1 = foldr1 (\ _ -> maybe 1 (_+ 1))

  first : t a -> a
  first = getFirst <<< foldMap1 asFirst

  last : t a -> a
  last = getLast <<< foldMap1 asLast

  sum1 : {{Semigroup (Sum a)}} -> t a -> a
  sum1 = getSum <<< foldMap1 asSum

  product1 : {{Semigroup (Product a)}} -> t a -> a
  product1 = getProduct <<< foldMap1 asProduct

  minimum : {{Ord a}} -> t a -> a
  minimum = getMin <<< foldMap1 asMin

  maximum : {{Ord a}} -> t a -> a
  maximum = getMax <<< foldMap1 asMax

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
