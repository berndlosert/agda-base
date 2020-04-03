{-# OPTIONS --type-in-type #-}

module Control.Optics.VL where

open import Prelude

open import Data.Functor.Contravariant
open import Data.Functor.Const
open import Data.Profunctor

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
    overlap {{applicativeSettable}} : Applicative F
    -- This should be the inverse of pure.
    unpure : F A -> A

open Settable {{...}}

instance
  settableIdentity : Settable Identity
  settableIdentity .unpure (identity: x) = x

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
to f k = const: <<< getConst <<< k <<< f

view : Getting A S A -> S -> A
view g = getConst <<< g const:

foldMapOf : Getting R S A -> (A -> R) -> S -> R
foldMapOf g k = g (k >>> const:) >>> getConst

foldrOf : Getting (Endo R) S A -> (A -> R -> R) -> R -> S -> R
foldrOf l f z = flip appEndo z <<< foldMapOf l (endo: <<< f)

foldlOf : Getting (Dual (Endo R)) S A -> (R -> A -> R) -> R -> S -> R
foldlOf l f z = rmap (flip appEndo z <<< getDual) (foldMapOf l (dual: <<< endo: <<< flip f))

toListOf : Getting (Endo (List A)) S A -> S -> List A
toListOf l = foldrOf l _::_ []

lengthOf : Getting (Dual (Endo Nat)) S A -> S -> Nat
lengthOf l = foldlOf l (\ a _ -> a + 1) 0

--preview : Getting (First A) S A -> S -> Maybe A
--preview l = getFirst <<< foldMapOf l (first: <<< just)

traverseOf' : {{_ : Functor F}}
  -> Getting (F R) S A -> (A -> F R) -> S -> F Unit
traverseOf' l f = map (const unit) <<< foldMapOf l f

forOf' : {{_ : Functor F}}
  -> Getting (F R) S A -> S -> (A -> F R) -> F Unit
forOf' = flip <<< traverseOf'

--------------------------------------------------------------------------------
-- ASetter operations
--------------------------------------------------------------------------------

ASetter : (S T A B : Set) -> Set
ASetter S T A B = (A -> Identity B) -> S -> Identity T

over : ASetter S T A B -> (A -> B) -> S -> T
over g k = g (k >>> identity:) >>> runIdentity

set : ASetter S T A B -> B -> S -> T
set l y = l (\ _ -> identity: y) >>> runIdentity

sets : ((A -> B) -> S -> T) -> ASetter S T A B
sets f k = f (k >>> runIdentity) >>> identity:

--------------------------------------------------------------------------------
-- Lenslike operations
--------------------------------------------------------------------------------

traverseOf : Lenslike F S T A B -> (A -> F B) -> S -> F T
traverseOf = identity

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

--:instance
  --eachList : Each (List A) (List B) A B
  --eachList .each = traverse

--------------------------------------------------------------------------------
-- Basic lens and traversals
--------------------------------------------------------------------------------

_fst : Lens (A * C) (B * C) A B
_fst k (x , y) = (_, y) <$> k x

sndL : Lens (A * B) (A * C) B C
sndL k (x , y) = (x ,_) <$> k y

leftT : Traversal (Either A C) (Either B C) A B
leftT f (left x) = left <$> f x
leftT _ (right y) = pure (right y)

rightT : Traversal (Either A B) (Either A C) B C
rightT f (right y) = right <$> f y
rightT _ (left x) = pure (left x)

justT : Traversal (Maybe A) (Maybe B) A B
justT f (just x) = just <$> f x
justT _ nothing = pure nothing

nothingT : Simple Traversal (Maybe A) Unit
nothingT f nothing = const nothing <$> f unit
nothingT _ j = pure j
