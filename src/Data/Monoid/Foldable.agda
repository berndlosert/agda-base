module Data.Monoid.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.All
open import Data.Monoid.Alt
open import Data.Monoid.Any
open import Data.Monoid.Dual
open import Data.Monoid.Endo
open import Data.Monoid.EndoM
open import Data.Monoid.Product
open import Data.Monoid.Sum
open import Data.Semigroup.Strict

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Monoid.All public
open Data.Monoid.Alt public
open Data.Monoid.Any public
open Data.Monoid.Dual public
open Data.Monoid.Endo public
open Data.Monoid.EndoM public
open Data.Monoid.Product public
open Data.Monoid.Sum public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    f m t : Type -> Type

-------------------------------------------------------------------------------
-- Foldable
-------------------------------------------------------------------------------

record Foldable (t : Type -> Type) : Type where
  field foldMap : {{Monoid b}} -> (a -> b) -> t a -> b

  foldr : (a -> b -> b) -> b -> t a -> b
  foldr {a} {b} step init xs = 
      appEndo (foldMap h xs) init
    where
      h : a -> Endo b
      h x = asEndo \ y -> step x y

  foldl : (b -> a -> b) -> b -> t a -> b
  foldl {b} {a} step init xs = 
      appEndo (getStrict $ getDual $ foldMap h xs) init
    where
      h : a -> Dual (Strict Endo b)
      h x = asDual $ asStrict $ asEndo \ y -> step y x

  fold : {{Monoid a}} -> t a -> a
  fold = foldMap id

  foldrM : {{Monad m}} -> (a -> b -> m b) -> b -> t a -> m b
  foldrM {m} {a} {b} step init xs = 
      appEndoM (foldMap h xs) init
    where
      h : a -> EndoM m b
      h x = asEndoM \ y -> step x y
      
  foldlM : {{Monad m}} -> (b -> a -> m b) -> b -> t a -> m b
  foldlM {m} {b} {a} step init xs = 
      appEndoM (getDual $ foldMap h xs) init
    where
      h : a -> Dual (EndoM m b)
      h x = asDual $ asEndoM \ y -> step y x

  toList : t a -> List a
  toList = foldMap (_:: [])

  concat : t (List a) -> List a
  concat = fold

  concatMap : (a -> List b) -> t a -> List b
  concatMap = foldMap

  length : t a -> Nat
  length = foldl (\ n _ -> suc n) 0

  find : (a -> Bool) -> t a -> Maybe a
  find {a} p = either just (const nothing) <<< foldlM step tt
    where
      step : Unit -> a -> Either a Unit
      step _ x = if p x then left x else right tt

  any : (a -> Bool) -> t a -> Bool
  any p = getAny <<< foldMap (asAny <<< p)

  all : (a -> Bool) -> t a -> Bool
  all p = getAll <<< foldMap (asAll <<< p)

  or : t Bool -> Bool
  or = any id

  and : t Bool -> Bool
  and = all id

  none : (a -> Bool) -> t a -> Bool
  none p = not <<< any p

  notNull : t a -> Bool
  notNull = any (const true)

  null : t a -> Bool
  null = not <<< notNull

  elem : {{Eq a}} -> a -> t a -> Bool
  elem x = any (_== x)

  notElem : {{Eq a}} -> a -> t a -> Bool
  notElem x = not <<< elem x

  defaulting : b -> (t a -> b) -> t a -> b
  defaulting d f xs = if null xs then d else f xs

  sum : {{Monoid (Sum a)}} -> t a -> a
  sum {a} = getSum <<< foldl step mempty
    where
      step : Sum a -> a -> Sum a
      step x y = x <> asSum y

  product : {{Monoid (Product a)}} -> t a -> a
  product {a} = getProduct <<< foldl step mempty
    where
      step : Product a -> a -> Product a
      step x y = x <> asProduct y

  traverse! : {{Applicative f}} -> (a -> f b) -> t a -> f Unit
  traverse! {f} {a} {b} h xs = foldr step (pure tt) xs
    where
      step : a -> f Unit -> f Unit
      step x y = h x *> y

  for! : {{Applicative f}} -> t a -> (a -> f b) -> f Unit
  for! = flip traverse!

  sequence! : {{Applicative f}} ->  t (f a) -> f Unit
  sequence! = traverse! id

  asum : {{Alternative f}} -> t (f a) -> f a
  asum = getAlt <<< foldMap asAlt

open Foldable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Identity : Foldable Identity
  Foldable-Identity .foldMap f x = f (runIdentity x)

  Foldable-Const : Foldable (Const a)
  Foldable-Const .foldMap _ _ = mempty

  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .foldMap f nothing = mempty
  Foldable-Maybe .foldMap f (just x) = f x

  Foldable-List : Foldable List
  Foldable-List .foldMap f [] = mempty
  Foldable-List .foldMap f (x :: xs) = f x <> foldMap f xs
