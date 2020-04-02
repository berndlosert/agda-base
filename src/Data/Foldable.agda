{-# OPTIONS --type-in-type #-}

module Data.Foldable where

open import Prelude

private
  variable
    A B S : Set
    F G M : Set -> Set

record Foldable (S : Set) : Set where
  field
    Elem : Set
    foldMap : {{_ : Monoid B}} -> (Elem -> B) -> S -> B

  fold : {{_ : Monoid Elem}} -> S -> Elem
  fold = foldMap identity

  foldr : (Elem -> B -> B) -> B -> S -> B
  foldr f b s = appEndo (foldMap (endo: <<< f) s) b

  foldl : (B -> Elem -> B) -> B -> S -> B
  foldl f b s =
    (appEndo <<< getDual) (foldMap (dual: <<< endo: <<< flip f) s) b

  foldrM : {{_ : Monad M}} -> (Elem -> B -> M B) -> B -> S -> M B
  foldrM f b s = let g k a b' = f a b' >>= k in
    foldl g return s b

  foldlM : {{_ : Monad M}} -> (B -> Elem -> M B) -> B -> S -> M B
  foldlM f b s = let g a k b' = f b' a >>= k in
    foldr g return s b

  null : S -> Bool
  null = untag <<< foldlM (\ _ _ -> left false) true

  nonempty : S -> Bool
  nonempty = not <<< null

  length : S -> Nat
  length = foldr (const suc) 0

  find : (Elem -> Bool) -> S -> Maybe Elem
  find p = let ensure' p = (\ _ -> maybeToLeft unit <<< ensure p) in
    leftToMaybe <<< foldlM (ensure' p) unit

  at : Nat -> S -> Maybe Elem
  at n = leftToMaybe <<< foldlM f 0
    where
      f : Nat -> Elem -> Elem + Nat
      f k a = if k == n then left a else right (suc k)

  any : (Elem -> Bool) -> S -> Bool
  any p = isJust <<< find p

  all : (Elem -> Bool) -> S -> Bool
  all p = not <<< any (not <<< p)

  module _ {{_ : Eq Elem}} where

    elem : Elem -> S -> Bool
    elem = any <<< _==_

    notElem : Elem -> S -> Bool
    notElem x = not <<< elem x

  module _ {{_ : Applicative F}} where

    traverse! : (Elem -> F B) -> S -> F Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : S -> (Elem -> F B) -> F Unit
    for! = flip traverse!

  module _ {{_ : Boolean Elem}} where

    or : S -> Elem
    or = foldr _||_ bottom

    and : S -> Elem
    and = foldr _&&_ top

open Foldable {{...}} public

instance
  foldableList : forall {A} -> Foldable (List A)
  foldableList {A} .Elem = A
  foldableList .foldMap f = \ where
    [] -> empty
    (a :: as) -> f a <> foldMap f as

  foldableString : Foldable String
  foldableString .Elem = Char
  foldableString .foldMap f s = foldMap f (unpack s)
