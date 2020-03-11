{-# OPTIONS --type-in-type #-}

module Control.Optics.VL where

open import Prelude

--------------------------------------------------------------------------------
-- Type classes used for characterizing optics
--------------------------------------------------------------------------------

-- Characterizes Setter
record Settable (F : Set -> Set) : Set where
  field
    overlap {{Applicative:Settable}} : Applicative F
    unwrap : forall {X} -> F X -> X

open Settable {{...}}

record Folding (F : Set -> Set) : Set where
  field
    overlap {{Applicative:Folding}} : Applicative F
    overlap {{Contravariant:Folding}} : Functor (Op Sets) Sets

open Folding {{...}}


--------------------------------------------------------------------------------
-- Van Laarhoven optics
--------------------------------------------------------------------------------

Optic : Set
Optic = (S T X Y : Set) -> Set

Optic' : Set
Optic' = (S X : Set) -> Set

Traversal : Optic
Traversal S T X Y = forall {F} {{_ : Applicative F}}
  -> (X -> F Y) -> S -> F T

Setter : Optic
Setter S T X Y = forall {F} {{_ : Settable F}}
  -> (X -> F Y) -> S -> F T

Fold : Optic
Fold S T X Y = forall {F} {{_ : Folding F}}
  -> (X -> F Y) -> S -> F T

Getter : Optic
Getter S T X Y = forall {F} {{_ : Getting F}}
  -> (X -> F Y) -> S -> F T
