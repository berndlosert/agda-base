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

--------------------------------------------------------------------------------
-- Optics ala Van Laarhoven
--------------------------------------------------------------------------------

Traversal : (S T X Y : Set) -> Set
Traversal S T X Y = forall {F} {{_ : Applicative F}}
  -> (X -> F Y) -> S -> F T

Setter : (S T X Y : Set) -> Set
Setter S T X Y = forall {F} {{_ : Settable F}}
  -> (X -> F Y) -> S -> F T

Fold : (S T X Y : Set) -> Set
Fold S T X Y = forall {F} {{_ : Applicative F}} {{_ : Contravariant F}}
  -> (X -> F Y) -> S -> F T

Getter : (S T X Y : Set) -> Set
Getter S T X Y = forall {F} {{_ : Functor F}} {{_ : Contravariant F}}
  -> (X -> F Y) -> S -> F T

Lens : (S T X Y : Set) -> Set
Lens S T X Y = forall {F} {{_ : Functor F}}
  -> (X -> F Y) -> S -> F T

--------------------------------------------------------------------------------
-- Getting operations
--------------------------------------------------------------------------------

Getting : (R S X : Set) -> Set
Getting R S X = (X -> const R X) -> S -> const R S

to : forall {S X} -> (S -> X) -> forall {R} -> Getting R S X
to k f = f <<< k

view : {S X : Set} -> Getting X S X -> S -> X
view g = g id

foldMapOf : forall {R S X} -> Getting R S X -> (X -> R) -> S -> R
foldMapOf = id

foldrOf : forall {R S X} -> Getting (R -> R) S X -> (X -> R -> R) -> R -> S -> R
foldrOf l f z = \ s -> foldMapOf l f s z

toListOf : forall {S X} -> Getting (List X -> List X) S X -> S -> List X
toListOf l = foldrOf l _::_ []

preview : forall {S X} -> Getting (Maybe X) S X -> S -> Maybe X
preview l = foldMapOf l just

--------------------------------------------------------------------------------
-- ASetter operations
--------------------------------------------------------------------------------

ASetter : (S T X Y : Set) -> Set
ASetter S T X Y = (X -> id Y) -> S -> id T

over : forall {S T X Y} -> ASetter S T X Y -> (X -> Y) -> S -> T
over = id

set : forall {S T X Y} -> ASetter S T X Y -> Y -> S -> T
set l y = l (const y)
