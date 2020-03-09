{-# OPTIONS --type-in-type #-}

module Control.Optics.Profunctor where

open import Data.Either
open import Data.Pair
open import Data.Profunctor
open import Prelude

--------------------------------------------------------------------------------
-- Types classes for characterizing profunctor optics
--------------------------------------------------------------------------------

-- Characterizes Lens
record Strong (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Strong}} : Profunctor Sets Sets P
    strong : forall {X Y Z} -> P X Y -> P (Z * X) (Z * Y)

open Strong {{...}} public

-- Characterizes Prism
record Choice (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Choice}} : Profunctor Sets Sets P
    choice : forall {X Y Z} -> P X Y -> P (Z + X) (Z + Y)

open Choice {{...}} public

-- Characterizes Grate
record Closed (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Closed}} : Profunctor Sets Sets P
    closed : {X Y Z : Set} -> P X Y -> P (Z -> X) (Z -> Y)

open Closed {{...}} public

-- Characterizes Traversal
record Wander (P : Set -> Set -> Set) : Set where
  constructor Wander:
  field
    overlap {{Strong:Wander}} : Strong P
    overlap {{Choice:Wander}} : Choice P
    wander : forall {X Y S T}
      -> (forall {F} {{_ : Applicative F}} -> (X -> F Y) -> S -> F T)
      -> P X Y -> P S T

open Wander {{...}}

--------------------------------------------------------------------------------
-- Profunctor optics
--------------------------------------------------------------------------------

Optic : Set
Optic = (X Y S T : Set) -> Set

Simple : Optic -> Set -> Set -> Set
Simple O X S = O X X S S

Adapter : Optic
Adapter X Y S T = forall {P} {{_ : Profunctor Sets Sets P}} -> P X Y -> P S T

Lens : Optic
Lens X Y S T = forall {P} {{_ : Strong P}} -> P X Y -> P S T

Prism : Optic
Prism X Y S T = forall {P} {{_ : Choice P}} -> P X Y -> P S T

Grate : Optic
Grate X Y S T = forall {P} {{_ : Closed P}} -> P X Y -> P S T

Traversal : Optic
Traversal X Y S T = forall {P} {{_ : Wander P}} -> P X Y -> P S T

Fold : Set -> Optic
Fold R X Y S T = (X -> R) -> S -> R

Getter : Optic
Getter X Y S T = forall {R} -> Fold R X Y S T

Review : Optic
Review X Y S T = Y -> T

Setter : Optic
Setter X Y S T = (X -> Y) -> S -> T

--------------------------------------------------------------------------------
-- Concrete optics
--------------------------------------------------------------------------------

-- Corresponds to Adapter
record Exchange (X Y S T : Set) : Set where
  constructor Exchange:
  field
    from : S -> X
    to : Y -> T

-- Corresponds to Lens
record Shop (X Y S T : Set) : Set where
  constructor Shop:
  field
    get : S -> X
    put : S -> Y -> T

-- Corresponds to Prism
record Market (X Y S T : Set) : Set where
  constructor Market:
  field
    build : Y -> T
    match : S -> T + X

-- Corresponds to Grate
record Grating (X Y S T : Set) : Set where
  constructor Grating:
  field
    degrating : ((S -> X) -> Y) -> T

-- Corresponds to Traversal
record Bazaar (P : Set -> Set -> Set) (X Y S T : Set) : Set where
  constructor Bazaar:
  field
    traverseOf : forall {F} {{_ : Applicative F}} -> P X (F Y) -> S -> F T

-- Corresponds to Setter
record Mapping (X Y S T : Set) : Set where
  constructor Mapping:
  field
    mapOf : (X -> Y) -> S -> T

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

Adapter: : forall {X Y S T} -> (S -> X) -> (Y -> T) -> Adapter X Y S T
Adapter: from to = bimap from to

Lens: : forall {X Y S T} -> (S -> X) -> (S -> Y -> T) -> Lens X Y S T
Lens: get put = bimap (split id get) (uncurry put) <<< strong

Prism: : forall {X Y S T} -> (Y -> T) -> (S -> T + X) -> Prism X Y S T
Prism: build match = bimap match untag <<< choice <<< rmap build

Grate: : forall {X Y S T} -> (((S -> X) -> Y) -> T) -> Grate X Y S T
Grate: degrating = bimap _#_ degrating <<< closed

Traversal: : forall {X Y S T}
  -> (forall {F} {{_ : Applicative F}} -> (X -> F Y) -> S -> F T)
  -> Traversal X Y S T
Traversal: traverse = wander traverse

Getter: : forall {X Y S T} -> (S -> X) -> Getter X Y S T
Getter: g = g >>>_

Review: : forall {X Y S T} -> (Y -> T) -> Review X Y S T
Review: = id

Setter: : forall {X Y S T} -> ((X -> Y) -> S -> T) -> Setter X Y S T
Setter: = id

--------------------------------------------------------------------------------
-- Profunctor instances
--------------------------------------------------------------------------------

instance
  Profunctor:Adapter : forall {X Y} -> Profunctor Sets Sets (Adapter X Y)
  Profunctor:Adapter .bimap f g adapter = bimap f g <<< adapter

  Profunctor:Exchange : forall {X Y} -> Profunctor Sets Sets (Exchange X Y)
  Profunctor:Exchange .bimap f g (Exchange: from to) =
    Exchange: (from <<< f) (g <<< to)

  Profunctor:Lens : forall {X Y} -> Profunctor Sets Sets (Lens X Y)
  Profunctor:Lens .bimap f g lens = bimap f g <<< lens

  Profunctor:Shop : forall {X Y} -> Profunctor Sets Sets (Shop X Y)
  Profunctor:Shop .bimap f g (Shop: get put) =
    Shop: (get <<< f) (\ s -> g <<< put (f s))

  Strong:Shop : forall {X Y} -> Strong (Shop X Y)
  Strong:Shop .strong (Shop: get put) = Shop: get' put'
    where
      get' put' : _
      get' (Pair: u s) = get s
      put' (Pair: u s) y = Pair: u (put s y)

  Profunctor:Prism : forall {X Y} -> Profunctor Sets Sets (Prism X Y)
  Profunctor:Prism .bimap f g prism = bimap f g <<< prism

  Profunctor:Market : forall {X Y} -> Profunctor Sets Sets (Market X Y)
  Profunctor:Market .bimap f g (Market: build match) =
      Market: (g <<< build) (lmap g <<< match <<< f)

  Choice:Market : forall {X Y} -> Choice (Market X Y)
  Choice:Market .choice (Market: build match) = Market: build' match'
    where
      build' match' : _
      build' y = right (build y)
      match' (left u) = left (left u)
      match' (right s) with match s
      ... | left t = left (right t)
      ... | right x = right x

  Profunctor:Grate : forall {X Y} -> Profunctor Sets Sets (Grate X Y)
  Profunctor:Grate .bimap f g grate = bimap f g <<< grate

  Profunctor:Grating : forall {X Y} -> Profunctor Sets Sets (Grating X Y)
  Profunctor:Grating .bimap f g (Grating: degrating) =
    Grating: \ d -> g (degrating \ k -> d (k <<< f))

  Closed:Grating : forall {X Y} -> Closed (Grating X Y)
  Closed:Grating .closed (Grating: degrating) =
    Grating: \ f x -> degrating \ k -> f \ g -> k (g x)

  Profunctor:Traversal : forall {X Y} -> Profunctor Sets Sets (Traversal X Y)
  Profunctor:Traversal .bimap f g traverse = bimap f g <<< traverse

  Profunctor:Bazaar : forall {P X Y} -> Profunctor Sets Sets (Bazaar P X Y)
  Profunctor:Bazaar .bimap f g (Bazaar: b) = Bazaar: \ h s -> g <$> b h (f s)

  Strong:Bazaar : forall {P X Y} -> Strong (Bazaar P X Y)
  Strong:Bazaar .strong (Bazaar: b) = Bazaar: \ where
    h (Pair: u s) -> Pair: u <$> b h s

  Choice:Bazaar : forall {P X Y} -> Choice (Bazaar P X Y)
  Choice:Bazaar .choice (Bazaar: b) = Bazaar: \ where
    h (right s) -> right <$> b h s
    h (left u) -> left <$> pure u

  Wander:Bazaar : forall {P X Y} -> Wander (Bazaar P X Y)
  Wander:Bazaar .wander w (Bazaar: b) = Bazaar: \ where
    h s -> w (b h) s

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

from : forall {X Y S T} -> Adapter X Y S T -> S -> X
to : forall {X Y S T} -> Adapter X Y S T -> Y -> T
from adapter = Exchange.from $ adapter $ Exchange: id id
to adapter = Exchange.to $ adapter $ Exchange: id id

get : forall {X Y S T} -> Lens X Y S T -> S -> X
put : forall {X Y S T} -> Lens X Y S T -> S -> Y -> T
get lens = Shop.get $ lens $ Shop: id (flip const)
put lens = Shop.put $ lens $ Shop: id (flip const)

build : forall {X Y S T} -> Prism X Y S T -> Y -> T
match : forall {X Y S T} -> Prism X Y S T -> S -> T + X
build prism = Market.build $ prism $ Market: id right
match prism = Market.match $ prism $ Market: id right

degrating : forall {X Y S T} -> Grate X Y S T -> ((S -> X) -> Y) -> T
degrating grate = Grating.degrating $ grate $ Grating: \ f -> f id

traverseOf : forall {X Y S T}
  -> Traversal X Y S T
  -> forall {F} {{_ : Applicative F}} -> (X -> F Y) -> S -> F T
traverseOf {X} {Y} traversal = Bazaar.traverseOf $ traversal $ bazaar
  where
    bazaar : Bazaar (hom Sets) X Y X Y
    bazaar = Bazaar: id

view : forall {X Y S T} -> Getter X Y S T -> S -> X
view getter = getter id

review : forall {X Y S T} -> Review X Y S T -> Y -> T
review = id

over : forall {X Y S T} -> Setter X Y S T -> (X -> Y) -> S -> T
over = id
