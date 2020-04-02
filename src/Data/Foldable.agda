{-# OPTIONS --type-in-type #-}

module Data.Foldable where

open import Prelude

private
  variable
    A B : Set
    F M : Set -> Set

record Foldable (T : Set -> Set) : Set where
  field
    foldMap : {{_ : Monoid B}} -> (A -> B) -> T A -> B

  fold : {{_ : Monoid A}} -> T A -> A
  fold = foldMap identity

  foldr : (A -> B -> B) -> B -> T A -> B
  foldr f b s = appEndo (foldMap (endo: <<< f) s) b

  foldl : (B -> A -> B) -> B -> T A -> B
  foldl f b s =
    (appEndo <<< getDual) (foldMap (dual: <<< endo: <<< flip f) s) b

  foldrM : {{_ : Monad M}} -> (A -> B -> M B) -> B -> T A -> M B
  foldrM f b s = let g k a b' = f a b' >>= k in
    foldl g return s b

  foldlM : {{_ : Monad M}} -> (B -> A -> M B) -> B -> T A -> M B
  foldlM f b s = let g a k b' = f b' a >>= k in
    foldr g return s b

  null : T A -> Bool
  null = untag <<< foldlM (\ _ _ -> left false) true

  nonempty : T A -> Bool
  nonempty = not <<< null

  length : T A -> Nat
  length = foldr (const suc) 0

  find : (A -> Bool) -> T A -> Maybe A
  find p = let ensure' p = (\ _ -> maybeToLeft unit <<< ensure p) in
    leftToMaybe <<< foldlM (ensure' p) unit

  at : Nat -> T A -> Maybe A
  at n = leftToMaybe <<< foldlM f 0
    where
      f : Nat -> A -> A + Nat
      f k a = if k == n then left a else right (suc k)

  any : (A -> Bool) -> T A -> Bool
  any p = isJust <<< find p

  all : (A -> Bool) -> T A -> Bool
  all p = not <<< any (not <<< p)

  module _ {{_ : Eq A}} where

    elem : A -> T A -> Bool
    elem = any <<< _==_

    notElem : A -> T A -> Bool
    notElem x = not <<< elem x

  module _ {{_ : Applicative F}} where

    traverse! : (A -> F B) -> T A -> F Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : T A -> (A -> F B) -> F Unit
    for! = flip traverse!

    sequence! : T (F A) -> F Unit
    sequence! = traverse! identity

  module _ {{_ : Boolean A}} where

    or : T A -> A
    or = foldr _||_ bottom

    and : T A -> A
    and = foldr _&&_ top

open Foldable {{...}} public

instance
  foldableList : Foldable List
  foldableList .foldMap f = \ where
    [] -> mempty
    (a :: as) -> f a <> foldMap f as
