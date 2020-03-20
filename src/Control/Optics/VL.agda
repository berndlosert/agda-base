{-# OPTIONS --type-in-type #-}

module Control.Optics.VL where

import Data.Functor.Contravariant
import Data.Functor.Const
import Data.List as List
import Prelude

open Data.Functor.Contravariant
open Data.Functor.Const public
open Prelude

private
  variable
    A B C R S T : Set
    F : Set -> Set

--------------------------------------------------------------------------------
-- Type classes used for characterizing optics
--------------------------------------------------------------------------------

-- Characterizes Setter
record Settable (F : Set -> Set) : Set where
  field
    overlap {{Applicative:Settable}} : Applicative F
    -- This should be the inverse of pure.
    unpure : F A -> A

open Settable {{...}}

instance
  Settable:Identity : Settable Identity
  Settable:Identity .unpure (value x) = x

--------------------------------------------------------------------------------
-- Optics ala Van Laarhoven
--------------------------------------------------------------------------------

Lenslike : (F : Set -> Set) (S T A B : Set) -> Set
Lenslike F S T A B = (A -> F B) -> S -> F T

Traversal : (S T A B : Set) -> Set
Traversal S T A B = forall {F} {{_ : Applicative F}}
  -> Lenslike F S T A B

Setter : (S T A B : Set) -> Set
Setter S T A B = forall {F} {{_ : Settable F}}
  -> Lenslike F S T A B

Fold : (S T A B : Set) -> Set
Fold S T A B = forall {F} {{_ : Applicative F}} {{_ : Contravariant F}}
  -> Lenslike F S T A B

Getter : (S T A B : Set) -> Set
Getter S T A B = forall {F} {{_ : Functor F}} {{_ : Contravariant F}}
  -> Lenslike F S T A B

Lens : (S T A B : Set) -> Set
Lens S T A B = forall {F} {{_ : Functor F}}
  -> Lenslike F S T A B

Simple : (Set -> Set -> Set -> Set -> Set) -> Set -> Set -> Set
Simple Optic S A = Optic S S A A

--------------------------------------------------------------------------------
-- Getting operations
--------------------------------------------------------------------------------

Getting : (R S A : Set) -> Set
Getting R S A = (A -> Const R A) -> S -> Const R S

to : (S -> A) -> Getting R S A
to f k = Const: <<< Const.get <<< k <<< f

view : Getting A S A -> S -> A
view g = Const.get <<< g Const:

foldMapOf : Getting R S A -> (A -> R) -> S -> R
foldMapOf g k = g (k >>> Const:) >>> Const.get

foldrOf : Getting (R -> R) S A -> (A -> R -> R) -> R -> S -> R
foldrOf l f z = \ s -> foldMapOf l f s z

toListOf : Getting (List A -> List A) S A -> S -> List A
toListOf l = foldrOf l _::_ []

preview : Getting (First A) S A -> S -> Maybe A
preview l = First.get <<< foldMapOf l (value <<< just)

traverseOf' : {{_ : Functor F}}
  -> Getting (F R) S A -> (A -> F R) -> S -> F Unit
traverseOf' l f = map (const tt) <<< foldMapOf l f

forOf' : {{_ : Functor F}}
  -> Getting (F R) S A -> S -> (A -> F R) -> F Unit
forOf' = flip <<< traverseOf'

--------------------------------------------------------------------------------
-- ASetter operations
--------------------------------------------------------------------------------

ASetter : (S T A B : Set) -> Set
ASetter S T A B = (A -> Identity B) -> S -> Identity T

over : ASetter S T A B -> (A -> B) -> S -> T
over g k = g (k >>> value) >>> Identity.run

set : ASetter S T A B -> B -> S -> T
set l y = l (\ _ -> value y) >>> Identity.run

sets : ((A -> B) -> S -> T) -> ASetter S T A B
sets f k = f (k >>> Identity.run) >>> value

--------------------------------------------------------------------------------
-- Lenslike operations
--------------------------------------------------------------------------------

traverseOf : Lenslike F S T A B -> (A -> F B) -> S -> F T
traverseOf = id

forOf : Lenslike F S T A B -> S -> (A -> F B) -> F T
forOf = flip

--------------------------------------------------------------------------------
-- Lens operations
--------------------------------------------------------------------------------

lens : (S -> A) -> (S -> B -> T) -> Lens S T A B
lens v u f s = u s <$> f (v s)

--------------------------------------------------------------------------------
-- Each and instances
--------------------------------------------------------------------------------

record Each (S T A B : Set) : Set where
  field
    each : Traversal S T A B

open Each {{...}} public

instance
  Each:List : Each (List A) (List B) A B
  Each:List .each = List.traverse

--------------------------------------------------------------------------------
-- Basic lens and traversals
--------------------------------------------------------------------------------

fst! : Lens (A * C) (B * C) A B
fst! k (x , y) = flip _,_ y <$> k x

snd! : Lens (A * B) (A * C) B C
snd! k (x , y) = _,_ x <$> k y

left! : Traversal (Either A C) (Either B C) A B
left! f (left x) = left <$> f x
left! _ (right y) = pure (right y)

right! : Traversal (Either A B) (Either A C) B C
right! f (right y) = right <$> f y
right! _ (left x) = pure (left x)

just! : Traversal (Maybe A) (Maybe B) A B
just! f (just x) = just <$> f x
just! _ nothing = pure nothing

nothing! : Simple Traversal (Maybe A) Unit
nothing! f nothing = const nothing <$> f tt
nothing! _ j = pure j
