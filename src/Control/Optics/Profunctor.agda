{-# OPTIONS --type-in-type #-}

module Control.Optics.Profunctor where

open import Data.Either
open import Data.Pair
open import Data.Profunctor
open import Prelude

private
  variable
    A B C R S T : Set
    F : Set -> Set
    P : Set -> Set -> Set

--------------------------------------------------------------------------------
-- Types classes for characterizing profunctor optics
--------------------------------------------------------------------------------

-- Characterizes Lens
record Strong (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Strong}} : Profunctor P
    strong : P A B -> P (C * A) (C * B)

open Strong {{...}} public

-- Characterizes Prism
record Choice (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Choice}} : Profunctor P
    choice : P A B -> P (C + A) (C + B)

open Choice {{...}} public

-- Characterizes Grate
record Closed (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Closed}} : Profunctor P
    closed : P A B -> P (C -> A) (C -> B)

open Closed {{...}} public

-- Characterizes Traversal
record Wander (P : Set -> Set -> Set) : Set where
  constructor Wander:
  field
    overlap {{Strong:Wander}} : Strong P
    overlap {{Choice:Wander}} : Choice P
    wander : (forall {F} {{_ : Applicative F}} -> (A -> F B) -> S -> F T)
      -> P A B -> P S T

open Wander {{...}}

--------------------------------------------------------------------------------
-- Profunctor optics
--------------------------------------------------------------------------------

Optic : Set
Optic = (A B S T : Set) -> Set

Simple : Optic -> Set -> Set -> Set
Simple O A S = O A A S S

Adapter : Optic
Adapter A B S T = forall {P} {{_ : Profunctor P}} -> P A B -> P S T

Lens : Optic
Lens A B S T = forall {P} {{_ : Strong P}} -> P A B -> P S T

Prism : Optic
Prism A B S T = forall {P} {{_ : Choice P}} -> P A B -> P S T

Grate : Optic
Grate A B S T = forall {P} {{_ : Closed P}} -> P A B -> P S T

Traversal : Optic
Traversal A B S T = forall {P} {{_ : Wander P}} -> P A B -> P S T

Fold : (R A S : Set) -> Set
Fold R A S = (A -> R) -> S -> R

Getter : (A S : Set) -> Set
Getter A S = forall {R} -> Fold R A S

Review : (B T : Set) -> Set
Review B T = B -> T

Setter : Optic
Setter A B S T = (A -> B) -> S -> T

--------------------------------------------------------------------------------
-- Concrete optics
--------------------------------------------------------------------------------

-- Corresponds to Adapter
record Exchange (A B S T : Set) : Set where
  constructor Exchange:
  field
    from : S -> A
    to : B -> T

-- Corresponds to Lens
record Shop (A B S T : Set) : Set where
  constructor Shop:
  field
    get : S -> A
    put : S -> B -> T

-- Corresponds to Prism
record Market (A B S T : Set) : Set where
  constructor Market:
  field
    build : B -> T
    match : S -> T + A

-- Corresponds to Grate
record Grating (A B S T : Set) : Set where
  constructor Grating:
  field
    degrating : ((S -> A) -> B) -> T

-- Corresponds to Traversal
record Bazaar (P : Set -> Set -> Set) (A B S T : Set) : Set where
  constructor Bazaar:
  field
    traverseOf : {{_ : Applicative F}} -> P A (F B) -> S -> F T

-- Corresponds to Setter
record Mapping (A B S T : Set) : Set where
  constructor Mapping:
  field
    mapOf : (A -> B) -> S -> T

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

Adapter: : (S -> A) -> (B -> T) -> Adapter A B S T
Adapter: from to = dimap from to

Lens: : (S -> A) -> (S -> B -> T) -> Lens A B S T
Lens: get put = dimap (split id get) (uncurry put) <<< strong

Prism: : (B -> T) -> (S -> T + A) -> Prism A B S T
Prism: build match = dimap match untag <<< choice <<< rmap build

Grate: : (((S -> A) -> B) -> T) -> Grate A B S T
Grate: degrating = dimap _#_ degrating <<< closed

Traversal: : (forall {F} {{_ : Applicative F}} -> (A -> F B) -> S -> F T)
  -> Traversal A B S T
Traversal: traverse = wander traverse

Getter: : (S -> A) -> Getter A S
Getter: g = g >>>_

Review: : (B -> T) -> Review B T
Review: = id

Setter: : ((A -> B) -> S -> T) -> Setter A B S T
Setter: = id

--------------------------------------------------------------------------------
-- Profunctor instances
--------------------------------------------------------------------------------

instance
  Profunctor:Adapter : Profunctor (Adapter A B)
  Profunctor:Adapter .dimap f g adapter = dimap f g <<< adapter

  Profunctor:Exchange : Profunctor (Exchange A B)
  Profunctor:Exchange .dimap f g (Exchange: from to) =
    Exchange: (from <<< f) (g <<< to)

  Profunctor:Lens : Profunctor (Lens A B)
  Profunctor:Lens .dimap f g lens = dimap f g <<< lens

  Profunctor:Shop : Profunctor (Shop A B)
  Profunctor:Shop .dimap f g (Shop: get put) =
    Shop: (get <<< f) (\ s -> g <<< put (f s))

  Strong:Shop : Strong (Shop A B)
  Strong:Shop .strong (Shop: get put) = Shop: get' put'
    where
      get' put' : _
      get' (u , s) = get s
      put' (u , s) y = (u , put s y)

  Profunctor:Prism : Profunctor (Prism A B)
  Profunctor:Prism .dimap f g prism = dimap f g <<< prism

  Profunctor:Market : Profunctor (Market A B)
  Profunctor:Market .dimap f g (Market: build match) =
      Market: (g <<< build) (first g <<< match <<< f)

  Choice:Market : Choice (Market A B)
  Choice:Market .choice (Market: build match) = Market: build' match'
    where
      build' match' : _
      build' y = right (build y)
      match' (left u) = left (left u)
      match' (right s) with match s
      ... | left t = left (right t)
      ... | right x = right x

  Profunctor:Grate : Profunctor (Grate A B)
  Profunctor:Grate .dimap f g grate = dimap f g <<< grate

  Profunctor:Grating : Profunctor (Grating A B)
  Profunctor:Grating .dimap f g (Grating: degrating) =
    Grating: \ d -> g (degrating \ k -> d (k <<< f))

  Closed:Grating : Closed (Grating A B)
  Closed:Grating .closed (Grating: degrating) =
    Grating: \ f x -> degrating \ k -> f \ g -> k (g x)

  Profunctor:Traversal : Profunctor (Traversal A B)
  Profunctor:Traversal .dimap f g traverse = dimap f g <<< traverse

  Profunctor:Bazaar : Profunctor (Bazaar P A B)
  Profunctor:Bazaar .dimap f g (Bazaar: b) = Bazaar: \ h s -> g <$> b h (f s)

  Strong:Bazaar : Strong (Bazaar P A B)
  Strong:Bazaar .strong (Bazaar: b) = Bazaar: \ where
    h (u , s) -> _,_ u <$> b h s

  Choice:Bazaar : Choice (Bazaar P A B)
  Choice:Bazaar .choice (Bazaar: b) = Bazaar: \ where
    h (right s) -> right <$> b h s
    h (left u) -> left <$> pure u

  Wander:Bazaar : Wander (Bazaar P A B)
  Wander:Bazaar .wander w (Bazaar: b) = Bazaar: \ where
    h s -> w (b h) s

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

from : Adapter A B S T -> S -> A
to : Adapter A B S T -> B -> T
from adapter = Exchange.from $ adapter $ Exchange: id id
to adapter = Exchange.to $ adapter $ Exchange: id id

get : Lens A B S T -> S -> A
put : Lens A B S T -> S -> B -> T
get lens = Shop.get $ lens $ Shop: id (flip const)
put lens = Shop.put $ lens $ Shop: id (flip const)

build : Prism A B S T -> B -> T
match : Prism A B S T -> S -> T + A
build prism = Market.build $ prism $ Market: id right
match prism = Market.match $ prism $ Market: id right

degrating : Grate A B S T -> ((S -> A) -> B) -> T
degrating grate = Grating.degrating $ grate $ Grating: \ f -> f id

traverseOf : Traversal A B S T
  -> (forall {F} {{_ : Applicative F}} -> (A -> F B) -> S -> F T)
traverseOf {A} {B} traversal = Bazaar.traverseOf $ traversal $ bazaar
  where
    bazaar : Bazaar Function A B A B
    bazaar = Bazaar: id

view : Getter A S -> S -> A
view getter = getter id

review : Review B T -> B -> T
review = id

over : Setter A B S T -> (A -> B) -> S -> T
over = id

--------------------------------------------------------------------------------
-- Operators
--------------------------------------------------------------------------------

_^#_ : forall {A S} -> S -> Getter A S -> A
_^#_ = flip view
