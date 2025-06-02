module Data.Functor.Recursive where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad
open import Control.Comonad.Cofree
open import Control.Monad.Free
open import Data.Functor.Compose
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c r t : Type
    f m w : Type -> Type

-------------------------------------------------------------------------------
-- Base functors
-------------------------------------------------------------------------------

record HasBase (t : Type) : Type where
  field Base : Type -> Type

Base : (t : Type) -> {{HasBase t}} -> Type -> Type
Base t {{prf}} = HasBase.Base prf

instance
  HasBase-Nat : HasBase Nat
  HasBase-Nat = record { Base = Maybe }

  HasBase-List : HasBase (List a)
  HasBase-List {a} = record { Base = Compose Maybe (Tuple a) }

-------------------------------------------------------------------------------
-- Recursive
-------------------------------------------------------------------------------

record Recursive (t : Type) {{_ : HasBase t}} : Type where
  field
    overlap {{Functor-Base}} : Functor (Base t)
    project : t -> Base t t

  cata : (Base t a -> a) -> t -> a
  cata alg = alg <<< map (cata alg) <<< project

  para : (Base t (Tuple t a) -> a) -> t -> a
  para alg = alg <<< map (_,_ <*> para alg) <<< project

  gcata : {{Comonad w}}
    -> (forall {b} -> Base t (w b) -> w (Base t b))
    -> (Base t (w a) -> a) -> t -> a
  gcata dist alg = alg <<< extract <<< h
    where h = dist <<< map (duplicate <<< map alg <<< h) <<< project

open Recursive {{...}} public

instance
  Recursive-Nat : Recursive Nat
  Recursive-Nat .project 0 = nothing
  Recursive-Nat .project (suc n) = just n

  Recursive-List : Recursive (List a)
  Recursive-List .project [] = asCompose nothing
  Recursive-List .project (x :: xs) = asCompose (just (x , xs))

-------------------------------------------------------------------------------
-- Corecursive
-------------------------------------------------------------------------------

record Corecursive (t : Type) {{_ : HasBase t}} : Type where
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
hylo coalg alg x = coalg (hylo coalg alg <$> alg x)

module _ {{_ : HasBase t}} where
  histo : {{Recursive t}} -> (Base t (Cofree (Base t) a) -> a) -> t -> a
  histo = gcata distHisto

  futu : {{Corecursive t}} -> (a -> Base t (Free (Base t) a)) -> a -> t
  futu = gana distFutu

-------------------------------------------------------------------------------
-- Fix
-------------------------------------------------------------------------------

data Fix (f : Type -> Type) : Type where
  aFix : f (Fix f) -> Fix f

instance
  HasBase-Fix : HasBase (Fix f)
  HasBase-Fix {f} = record { Base = f}

  Recursive-Fix : {{Functor f}} -> Recursive (Fix f)
  Recursive-Fix .project (aFix x) = x

  Show-Fix : {{forall {a} -> {{Show a}} -> Show (f a)}} -> Show (Fix f)
  Show-Fix .show = showDefault
  Show-Fix .showsPrec prec (aFix fx) = showsUnaryWith showsPrec "aFix" prec fx