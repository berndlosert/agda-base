{-# OPTIONS --type-in-type #-}

module Data.Generics where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    c p : Set

-------------------------------------------------------------------------------
-- Core Rep types
-------------------------------------------------------------------------------

data V1 (p : Set) : Set where

data U1 (p : Set) : Set where
  u1 : U1 p

data S1 (f g : Set -> Set) (p : Set) : Set where
  l1 : f p -> S1 f g p
  r1 : g p -> S1 f g p

data P1 (f g : Set -> Set) (p : Set) : Set where
  p1 : f p -> g p -> P1 f g p

record Rec0 (c p : Set) : Set where
  constructor rec0
  field unRec0 : c

open Rec0 public

record Par1 (p : Set) : Set where
  constructor par1
  field unPar1 : p

open Par1 public

data I : Set where
  D R C F : I

data Meta : Set where
  MetaData : String -> Meta
  MetaCons : String -> Meta
  MetaFld : Maybe String -> Meta

record M1 (i : I) (c : Meta) (f : Set -> Set) (p : Set) : Set where
  constructor m1
  field unM1 : f p

D1 = M1 D
C1 = M1 C
F1 = M1 F

-------------------------------------------------------------------------------
-- Generic
-------------------------------------------------------------------------------

record Generic (a : Set) : Set where
  field
    Rep : (b : Set) -> {{a === b}} -> Set -> Set
    toRep : a -> Rep a p
    fromRep : Rep a p -> a

open Generic {{...}} public
