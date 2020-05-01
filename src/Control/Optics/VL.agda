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
  copointedIdentity : Copointed Identity
  copointedIdentity .extract = runIdentity

--------------------------------------------------------------------------------
-- Optics ala Van Laarhoven
--------------------------------------------------------------------------------

Traversal : (S T A B : Set) -> Set
Traversal S T A B = ∀ {F} {{_ : Applicative F}}
  -> (A -> F B) -> S -> F T

Setter : (S T A B : Set) -> Set
Setter S T A B = ∀ {F} {{_ : Applicative F}} {{_ : Copointed F}}
  -> (A -> F B) -> S -> F T

Fold : (S T A B : Set) -> Set
Fold S T A B = ∀ {F} {{_ : Applicative F}} {{_ : Contravariant F}}
  -> (A -> F B) -> S -> F T

Lens : (S T A B : Set) -> Set
Lens S T A B = ∀ {F} {{_ : Functor F}}
  -> (A -> F B) -> S -> F T

Getter : (S T A B : Set) -> Set
Getter S T A B = ∀ {F} {{_ : Functor F}} {{_ : Contravariant F}}
  -> (A -> F B) -> S -> F T

Simple : (Set -> Set -> Set -> Set -> Set) -> Set -> Set -> Set
Simple Optic S A = Optic S S A A

--------------------------------------------------------------------------------
-- Getting operations
--------------------------------------------------------------------------------

Getting : (R S A : Set) -> Set
Getting R S A = (A -> Const R A) -> S -> Const R S

to : (S -> A) -> Getting R S A
to f k = const: ∘ getConst ∘ k ∘ f

view : Getting A S A -> S -> A
view g = getConst ∘ g const:

foldMapOf : Getting R S A -> (A -> R) -> S -> R
foldMapOf g k = getConst ∘ g (const: ∘ k)

foldrOf : Getting (Endo R) S A -> (A -> R -> R) -> R -> S -> R
foldrOf l f z = flip appEndo z ∘ foldMapOf l (endo: ∘ f)

foldlOf : Getting (Dual (Endo R)) S A -> (R -> A -> R) -> R -> S -> R
foldlOf l f z = rmap (flip appEndo z ∘ getDual) (foldMapOf l (dual: ∘ endo: ∘ flip f))

toListOf : Getting (Endo (List A)) S A -> S -> List A
toListOf l = foldrOf l _::_ []

lengthOf : Getting (Dual (Endo Nat)) S A -> S -> Nat
lengthOf l = foldlOf l (λ a _ -> a + 1) 0

preview : Getting (Maybe (First A)) S A -> S -> Maybe A
preview l = map getFirst ∘ foldMapOf l (just ∘ first:)

traverseOf! : {{_ : Functor F}}
  -> Getting (F R) S A -> (A -> F R) -> S -> F Unit
traverseOf! l f = map (const unit) ∘ foldMapOf l f

forOf! : {{_ : Functor F}}
  -> Getting (F R) S A -> S -> (A -> F R) -> F Unit
forOf! = flip ∘ traverseOf!

--------------------------------------------------------------------------------
-- ASetter operations
--------------------------------------------------------------------------------

ASetter : (S T A B : Set) -> Set
ASetter S T A B = (A -> Identity B) -> S -> Identity T

over : ASetter S T A B -> (A -> B) -> S -> T
over g k = runIdentity ∘ g (identity: ∘ k)

set : ASetter S T A B -> B -> S -> T
set l y = runIdentity ∘ l (λ _ -> identity: y)

sets : ((A -> B) -> S -> T) -> ASetter S T A B
sets f k = identity: ∘ f (runIdentity ∘ k)

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
