module Data.Functor.Recursive where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b r t : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Base functors
-------------------------------------------------------------------------------

record HasBase (t : Set) : Set where
  field Base : Set -> Set

Base : (t : Set) -> {{HasBase t}} -> Set -> Set
Base t {{prf}} = HasBase.Base prf

-------------------------------------------------------------------------------
-- Recursive
-------------------------------------------------------------------------------

record Recursive (t : Set) {{_ : HasBase t}} : Set where
  field
    overlap {{Functor-Base}} : Functor (Base t)
    project : t -> Base t t

  cata : (Base t a -> a) -> t -> a
  cata alg = alg <<< map (cata alg) <<< project

  para : (Base t (Pair t a) -> a) -> t -> a
  para alg = alg <<< map (_,_ <*> para alg) <<< project

open Recursive {{...}} public

-------------------------------------------------------------------------------
-- Corecursive
-------------------------------------------------------------------------------

record Corecursive (t : Set) {{_ : HasBase t}} : Set where
  field
    overlap {{Functor-Base}} : Functor (Base t)
    embed : Base t t -> t

  ana : (a -> Base t a) -> a -> t
  ana coalg = embed <<< map (ana coalg) <<< coalg

  apo : (a -> Base t (Either t a)) -> a -> t
  apo coalg = embed <<< map (either id (apo coalg)) <<< coalg

open Corecursive {{...}} public

-------------------------------------------------------------------------------
-- Other recursion schemes
-------------------------------------------------------------------------------

hylo : {{Functor f}} -> (f b -> b) -> (a -> f a) -> a -> b
hylo coalg alg x = coalg $ hylo coalg alg <$> alg x

-------------------------------------------------------------------------------
-- Fix
-------------------------------------------------------------------------------

data Fix (f : Set -> Set) : Set where
  asFix : f (Fix f) -> Fix f

instance
  HasBase-Fix : HasBase (Fix f)
  HasBase-Fix {f} = record { Base = f}

  Recursive-Fix : {{Functor f}} -> Recursive (Fix f)
  Recursive-Fix .project (asFix x) = x

-------------------------------------------------------------------------------
-- NatF
-------------------------------------------------------------------------------

data NatF (r : Set) : Set where
  zero : NatF r
  suc : r -> NatF r

instance
  HasBase-Nat : HasBase Nat
  HasBase-Nat = record { Base = NatF }

  Functor-NatF : Functor NatF
  Functor-NatF .map f = \ where
    zero -> zero
    (suc n) -> suc (f n)

  Show-NatF : {{Show r}} -> Show (NatF r)
  Show-NatF .showsPrec prec = \ where
    zero -> showString "zero"
    (suc n) -> showParen (prec > appPrec)
      (showString "suc " <<< showsPrec appPrec+1 n)

  Recursive-Nat : Recursive Nat
  Recursive-Nat .project 0 = zero
  Recursive-Nat .project (suc n) = suc n

-------------------------------------------------------------------------------
-- ListF
-------------------------------------------------------------------------------

data ListF (a r : Set) : Set where
  [] : ListF a r
  _::_ : a -> r -> ListF a r

instance
  HasBase-List : HasBase (List a)
  HasBase-List {a} = record { Base = ListF a }

  Functor-ListF : Functor (ListF a)
  Functor-ListF .map f = \ where
    [] -> []
    (x :: xs) -> x :: f xs

  Show-ListF : {{Show a}} -> {{Show r}} -> Show (ListF a r)
  Show-ListF .showsPrec prec = \ where
    [] -> showString "[]"
    (x :: xs) -> showParen (prec > appPrec)
      (showsPrec appPrec+1 x <<< showString " :: " <<< showsPrec 0 xs)

  Recursive-List : Recursive (List a)
  Recursive-List .project [] = []
  Recursive-List .project (x :: xs) = x :: xs