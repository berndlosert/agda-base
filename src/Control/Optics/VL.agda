{-# OPTIONS --type-in-type #-}

module Control.Optics.VL where

import Data.Functor.Identity
import Data.Functor.Contravariant
import Data.Functor.Const
import Data.List as List
import Prelude

open Data.Functor.Identity public
open Data.Functor.Contravariant
open Data.Functor.Const public
open Prelude

--------------------------------------------------------------------------------
-- Type classes used for characterizing optics
--------------------------------------------------------------------------------

-- Characterizes Setter
record Settable (F : Set -> Set) : Set where
  field
    overlap {{Applicative:Settable}} : Applicative F
    -- This should be the inverse of pure.
    unpure : forall {X} -> F X -> X

open Settable {{...}}

instance
  Settable:Identity : Settable Identity
  Settable:Identity .unpure (Identity: x) = x

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

Simple : (Set -> Set -> Set -> Set -> Set) -> Set -> Set -> Set
Simple Optic S X = Optic S S X X

--------------------------------------------------------------------------------
-- Getting operations
--------------------------------------------------------------------------------

Getting : (R S X : Set) -> Set
Getting R S X = (X -> Const R X) -> S -> Const R S

to : forall {S X} -> (S -> X) -> forall {R} -> Getting R S X
to f k = Const: <<< Const.get <<< k <<< f

view : {S X : Set} -> Getting X S X -> S -> X
view g = Const.get <<< g Const:

foldMapOf : forall {R S X} -> Getting R S X -> (X -> R) -> S -> R
foldMapOf g k = g (k >>> Const:) >>> Const.get

foldrOf : forall {R S X}
  -> Getting (R -> R) S X -> (X -> R -> R) -> R -> S -> R
foldrOf l f z = \ s -> foldMapOf l f s z

toListOf : forall {S X} -> Getting (List X -> List X) S X -> S -> List X
toListOf l = foldrOf l _::_ []

preview : forall {S X} -> Getting (First X) S X -> S -> Maybe X
preview l = First.get <<< foldMapOf l (First: <<< just)

traverseOf' : forall {F R S X} {{_ : Functor F}}
  -> Getting (F R) S X -> (X -> F R) -> S -> F Unit
traverseOf' l f = map (const tt) <<< foldMapOf l f

forOf' : forall {F R S X} {{_ : Functor F}}
  -> Getting (F R) S X -> S -> (X -> F R) -> F Unit
forOf' = flip <<< traverseOf'

--------------------------------------------------------------------------------
-- ASetter operations
--------------------------------------------------------------------------------

ASetter : (S T X Y : Set) -> Set
ASetter S T X Y = (X -> Identity Y) -> S -> Identity T

over : forall {S T X Y} -> ASetter S T X Y -> (X -> Y) -> S -> T
over g k = g (k >>> Identity:) >>> Identity.run

set : forall {S T X Y} -> ASetter S T X Y -> Y -> S -> T
set l y = l (\ _ -> Identity: y) >>> Identity.run

sets : forall {S T X Y} -> ((X -> Y) -> S -> T) -> ASetter S T X Y
sets f k = f (k >>> Identity.run) >>> Identity:

--------------------------------------------------------------------------------
-- Lenslike operations
--------------------------------------------------------------------------------

Lenslike : (F : Set -> Set) (S T X Y : Set) -> Set
Lenslike F S T X Y = (X -> F Y) -> S -> F T

traverseOf : forall {F S T X Y} ->
  Lenslike F S T X Y -> (X -> F Y) -> S -> F T
traverseOf = id

forOf : forall {F S T X Y} ->
  Lenslike F S T X Y -> S -> (X -> F Y) -> F T
forOf = flip

--------------------------------------------------------------------------------
-- Lens operations
--------------------------------------------------------------------------------

lens : forall {S T X Y} -> (S -> X) -> (S -> Y -> T) -> Lens S T X Y
lens v u f s = u s <$> f (v s)

--------------------------------------------------------------------------------
-- Each definition and instances
--------------------------------------------------------------------------------

record Each (S T X Y : Set) : Set where
  field
    each : Traversal S T X Y

open Each {{...}} public

instance
  Each:List : forall {X Y} -> Each (List X) (List Y) X Y
  Each:List .each = List.traverse

--------------------------------------------------------------------------------
-- Basic lens and traversals
--------------------------------------------------------------------------------

fst! : forall {X X' Y} -> Lens (X * Y) (X' * Y) X X'
fst! k (Pair: x y) = flip Pair: y <$> k x

snd! : forall {X Y Y'} -> Lens (X * Y) (X * Y') Y Y'
snd! k (Pair: x y) = Pair: x <$> k y

left! : forall {X X' Y} -> Traversal (Either X Y) (Either X' Y) X X'
left! f (left x) = left <$> f x
left! _ (right y) = pure (right y)

right! : forall {X Y Y'} -> Traversal (Either X Y) (Either X Y') Y Y'
right! f (right y) = right <$> f y
right! _ (left x) = pure (left x)

just! : forall {X X'} -> Traversal (Maybe X) (Maybe X') X X'
just! f (just x) = just <$> f x
just! _ nothing = pure nothing

nothing! : forall {X} -> Simple Traversal (Maybe X) Unit
nothing! f nothing = const nothing <$> f tt
nothing! _ j = pure j
