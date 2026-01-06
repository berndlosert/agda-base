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
open import Data.Monoid.Product
open import Data.Monoid.Sum

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Monoid.All public
open Data.Monoid.Alt public
open Data.Monoid.Any public
open Data.Monoid.Dual public
open Data.Monoid.Endo public
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
  foldr step init xs = appEndo (foldMap (asEndo <<< step) xs) init

  foldl : (b -> a -> b) -> b -> t a -> b
  foldl {b} {a} step init xs = appEndo (foldMap g xs) id init
    where
      g : a -> Endo (b -> b)
      g x = asEndo \ k y -> k $! step y x

  fold : {{Monoid a}} -> t a -> a
  fold = foldMap id

  foldlM : {{Monad m}} -> (b -> a -> m b) -> b -> t a -> m b
  foldlM {m} {b} {a} step init xs = foldr step1 pure xs init
    where
      step1 : a -> (b -> m b) -> b -> m b
      step1 x k acc = k =<< step acc x

  foldrM : {{Monad m}} -> (a -> b -> m b) -> b -> t a -> m b
  foldrM {m} {a} {b} step init xs = foldl step1 pure xs init
    where
      step1 : (b -> m b) -> a -> b -> m b
      step1 k x acc = k =<< step x acc

  toList : t a -> List a
  toList = foldMap (_:: [])

  concat : t (List a) -> List a
  concat = fold

  concatMap : (a -> List b) -> t a -> List b
  concatMap = foldMap

  length : t a -> Nat
  length = foldr (const suc) 0

  find : (a -> Bool) -> t a -> Maybe a
  find {a} p = either just (const nothing) <<< foldlM step tt
    where
      step : Unit -> a -> Either a Unit
      step _ x = if p x then left x else right tt

  any : (a -> Bool) -> t a -> Bool
  any p = getAny <<< foldMap (asAny <<< p)

  all : (a -> Bool) -> t a -> Bool
  all p = getAll <<< foldMap (asAll <<< p)

  none : (a -> Bool) -> t a -> Bool
  none p = not <<< any p

  or : t Bool -> Bool
  or = any id

  and : t Bool -> Bool
  and = all id

  null : t a -> Bool
  null = foldr (\ _ _ -> false) true

  notNull : t a -> Bool
  notNull = not <<< null

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

  _elem_ : {{Eq a}} -> a -> t a -> Bool
  _elem_ x = any (_== x)

  _notElem_ : {{Eq a}} -> a -> t a -> Bool
  x notElem xs = not (x elem xs)

  traverse' : {{Applicative f}} -> (a -> f b) -> t a -> f Unit
  traverse' f = foldr (\ x y -> f x *> y) (pure tt)

  for' : {{Applicative f}} -> t a -> (a -> f b) -> f Unit
  for' = flip traverse'

  sequence' : {{Applicative f}} ->  t (f a) -> f Unit
  sequence' = traverse' id

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
  Foldable-Maybe .foldMap f = \ where
    nothing -> mempty
    (just x) -> f x

  Foldable-List : Foldable List
  Foldable-List .foldMap f = \ where
    [] -> mempty
    (x :: xs) -> f x <> foldMap f xs
