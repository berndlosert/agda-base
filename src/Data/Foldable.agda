{-# OPTIONS --type-in-type #-}

module Data.Foldable where

open import Control.Applicative
open import Control.Monad
open import Data.Bool
open import Data.Function
open import Data.Functor
open import Data.Eq
open import Data.Monoid
open import Data.Nat
open import Data.Semigroup
open import Data.Semiring
open import Prim

private
  variable
    A B S : Set
    F M : Set -> Set

--------------------------------------------------------------------------------
-- Step (used for short-circuiting)
--------------------------------------------------------------------------------

data Step (A B : Set) : Set where
  break : A -> Step A B
  continue : B -> Step A B

instance
  functorStep : Functor (Step A)
  functorStep .map f = \ where
    (break a) -> break a
    (continue x) -> continue (f x)

  applicativeStep : Applicative (Step A)
  applicativeStep .pure = continue
  applicativeStep ._<*>_ = \ where
    (break a) _ -> break a
    (continue f) x -> map f x

  monadStep : Monad (Step A)
  monadStep ._>>=_ = \ where
    (break a) k -> break a
    (continue x) k -> k x

--------------------------------------------------------------------------------
-- IsFoldable
--------------------------------------------------------------------------------

record IsFoldable (S A : Set) : Set where
  field
    foldMap : {{_ : Monoid B}} -> (A -> B) -> S -> B

  fold : {{_ : Monoid A}} -> S -> A
  fold = foldMap id

  foldr : (A -> B -> B) -> B -> S -> B
  foldr f b as = fromEndo (foldMap (toEndo <<< f) as) b

  foldl : (B -> A -> B) -> B -> S -> B
  foldl f b as =
    (fromEndo <<< fromDual) (foldMap (toDual <<< toEndo <<< flip f) as) b

  foldrM : {{_ : Monad M}} -> (A -> B -> M B) -> B -> S -> M B
  foldrM f b as = let g k a b' = f a b' >>= k in
    foldl g return as b

  foldlM : {{_ : Monad M}} -> (B -> A -> M B) -> B -> S -> M B
  foldlM f b as = let g a k b' = f b' a >>= k in
    foldr g return as b

  -- Short-circuiting version of foldr'
  foldr' : (A -> B -> Step B B) -> B -> S -> B
  foldr' f b s with foldrM f b s
  ... | (break b') = b'
  ... | (continue b') = b'

  -- Short-circuiting version of foldl'
  foldl' : (B -> A -> Step B B) -> B -> S -> B
  foldl' f b s with foldlM f b s
  ... | (break b') = b'
  ... | (continue b') = b'

  count : S -> Nat
  count = fromSum <<< foldMap (const $ toSum 1)

  all : (A -> Bool) -> S -> Bool
  all p = fromAll <<< foldMap (toAll <<< p)

  any : (A -> Bool) -> S -> Bool
  any p = fromAny <<< foldMap (toAny <<< p)

  null : S -> Bool
  null = not <<< any (const true)

  --find : (A -> Bool) -> S -> Maybe A
  --find p = let ensure' p = (\ _ -> maybeToLeft unit <<< ensure p) in
  --  leftToMaybe <<< foldlM (ensure' p) unit

  --at : Nat -> S -> Maybe A
  --at n = leftToMaybe <<< foldlM f 0
  --  where
  --    f : Nat -> A -> Either A Nat
  --    f k a = if k == n then left a else right (suc k)

  module _ {{_ : Eq A}} where

    elem : A -> S -> Bool
    elem = any <<< _==_

    notElem : A -> S -> Bool
    notElem a s = not (elem a s)

  module _ {{_ : Monoid A}} where

    concat : S -> A
    concat = foldr _<>_ mempty

  module _ {{_ : Applicative F}} where

    traverse! : (A -> F B) -> S -> F Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : S -> (A -> F B) -> F Unit
    for! = flip traverse!

open IsFoldable {{...}} public

sequence! : {{_ : Applicative F}} {{_ : IsFoldable S (F A)}} -> S -> F Unit
sequence! = traverse! id

module _ {{_ : IsFoldable S Bool}} where

  or : S -> Bool
  or = foldr _||_ false

  and : S -> Bool
  and = foldr _&&_ true

--------------------------------------------------------------------------------
-- Foldable
--------------------------------------------------------------------------------

Foldable : (Set -> Set) -> Set
Foldable F = forall {A} -> IsFoldable (F A) A
