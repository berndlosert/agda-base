{-# OPTIONS --type-in-type #-}

module Control.Optics.VL where

open import Prelude

private
  variable
    A B C R S T : Set
    F : Set -> Set

--------------------------------------------------------------------------------
-- Additional Type classes used for characterizing optics
--------------------------------------------------------------------------------

record Copointed (F : Set -> Set) : Set where
  field extract : F A -> A

open Copointed {{...}}

instance
  copointedId : Copointed Id
  copointedId .extract = fromId

--------------------------------------------------------------------------------
-- Optics ala Van Laarhoven
--------------------------------------------------------------------------------

Traversal : (S T A B : Set) -> Set
Traversal S T A B = forall {F} {{_ : Applicative F}}
  -> (A -> F B) -> S -> F T

Setter : (S T A B : Set) -> Set
Setter S T A B = forall {F} {{_ : Applicative F}} {{_ : Copointed F}}
  -> (A -> F B) -> S -> F T

Fold : (S T A B : Set) -> Set
Fold S T A B = forall {F} {{_ : Applicative F}} {{_ : Contravariant F}}
  -> (A -> F B) -> S -> F T

Lens : (S T A B : Set) -> Set
Lens S T A B = forall {F} {{_ : Functor F}}
  -> (A -> F B) -> S -> F T

Getter : (S T A B : Set) -> Set
Getter S T A B = forall {F} {{_ : Functor F}} {{_ : Contravariant F}}
  -> (A -> F B) -> S -> F T

Simple : (Set -> Set -> Set -> Set -> Set) -> Set -> Set -> Set
Simple Optic S A = Optic S S A A

--------------------------------------------------------------------------------
-- Getting operations
--------------------------------------------------------------------------------

Getting : (R S A : Set) -> Set
Getting R S A = (A -> Const R A) -> S -> Const R S

to : (S -> A) -> Getting R S A
to f k = toConst <<< fromConst <<< k <<< f

view : Getting A S A -> S -> A
view g = fromConst <<< g toConst

foldMapOf : Getting R S A -> (A -> R) -> S -> R
foldMapOf g k = g (k >>> toConst) >>> fromConst

foldrOf : Getting (Endo R) S A -> (A -> R -> R) -> R -> S -> R
foldrOf l f z = flip fromEndo z <<< foldMapOf l (toEndo <<< f)

foldlOf : Getting (Dual (Endo R)) S A -> (R -> A -> R) -> R -> S -> R
foldlOf l f z = rmap (flip fromEndo z <<< fromDual) (foldMapOf l (toDual <<< toEndo <<< flip f))

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
ASetter S T A B = (A -> Id B) -> S -> Id T

over : ASetter S T A B -> (A -> B) -> S -> T
over g k = g (k >>> toId) >>> fromId

set : ASetter S T A B -> B -> S -> T
set l y = l (\ _ -> toId y) >>> fromId

sets : ((A -> B) -> S -> T) -> ASetter S T A B
sets f k = f (k >>> fromId) >>> toId

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
  eachList : Each (List A) (List B) A B
  eachList .each = traverse

--------------------------------------------------------------------------------
-- Basic lens and traversals
--------------------------------------------------------------------------------

#fst : Lens (Pair A C) (Pair B C) A B
#fst k (a , c) = (_, c) <$> k a

#snd : Lens (Pair A B) (Pair A C) B C
#snd k (x , y) = (x ,_) <$> k y

#left : Traversal (Either A C) (Either B C) A B
#left f (left x) = left <$> f x
#left _ (right y) = pure (right y)

#right : Traversal (Either A B) (Either A C) B C
#right f (right y) = right <$> f y
#right _ (left x) = pure (left x)

#just : Traversal (Maybe A) (Maybe B) A B
#just f (just x) = just <$> f x
#just _ nothing = pure nothing

#nothing : Simple Traversal (Maybe A) Unit
#nothing f nothing = const nothing <$> f unit
#nothing _ j = pure j
