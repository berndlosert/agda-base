module Data.Functor.Recursive where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad
open import Control.Comonad.Cofree
open import Control.Monad.Free
open import Data.Functor.Identity
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c r t : Set
    f m w : Set -> Set

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

  gcata : {{Comonad w}}
    -> (forall {b} -> Base t (w b) -> w (Base t b))
    -> (Base t (w a) -> a) -> t -> a
  gcata dist alg = alg <<< extract <<< h
    where h = dist <<< map (duplicate <<< map alg <<< h) <<< project

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

  gana : {{Monad m}}
    -> (forall {b} -> m (Base t b) -> Base t (m b))
    -> (a -> Base t (m a)) -> a -> t
  gana dist coalg = h <<< pure <<< coalg
    where h = embed <<< map (h <<< map coalg <<< join) <<< dist

open Corecursive {{...}} public

-------------------------------------------------------------------------------
-- Distribute laws
-------------------------------------------------------------------------------

distCata : {{Functor f}} -> f (Identity a) -> Identity (f a)
distCata = asIdentity <<< map runIdentity

distAna : {{Functor f}} -> Identity (f a) -> f (Identity a)
distAna = map asIdentity <<< runIdentity

distHisto : {{Functor f}} -> f (Cofree f a) -> Cofree f (f a)
distHisto fc = \ where
  .Cofree.value -> map extract fc
  .Cofree.unwrap -> map (distHisto <<< Cofree.unwrap) fc

distFutu : {{Functor f}} -> Free f (f a) -> f (Free f a)
distFutu = distFutu <<< interpretFree liftFree

-------------------------------------------------------------------------------
-- Other recursion schemes
-------------------------------------------------------------------------------

fix : (a -> a) -> a
fix f = f (fix f)

loeb : {{Functor f}} -> f (f a -> a) -> f a
loeb x = go where go = map (_$ go) x

moeb : (((a -> b) -> b) -> c -> a) -> c -> a
moeb f x = go where go = f (_$ go) x

hylo : {{Functor f}} -> (f b -> b) -> (a -> f a) -> a -> b
hylo coalg alg x = coalg $ hylo coalg alg <$> alg x

module _ {{_ : HasBase t}} where
  histo : {{Recursive t}} -> (Base t (Cofree (Base t) a) -> a) -> t -> a
  histo = gcata distHisto

  futu : {{Corecursive t}} -> (a -> Base t (Free (Base t) a)) -> a -> t
  futu = gana distFutu

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

  Show-Fix : {{forall {a} -> {{Show a}} -> Show (f a)}} -> Show (Fix f)
  Show-Fix .show = showDefault
  Show-Fix .showsPrec prec (asFix fx) = showsUnaryWith showsPrec "asFix" prec fx

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
  Show-NatF .show = showDefault
  Show-NatF .showsPrec prec = \ where
    zero -> "zero"
    (suc n) -> showsUnaryWith showsPrec "suc" prec n

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
  Show-ListF .show = showDefault
  Show-ListF .showsPrec prec = \ where
    [] -> "[]"
    (x :: xs) -> showParen (prec > appPrec)
      (showsPrec appPrec+1 x <> " :: " <> showsPrec 0 xs)

  Recursive-List : Recursive (List a)
  Recursive-List .project [] = []
  Recursive-List .project (x :: xs) = x :: xs