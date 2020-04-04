{-# OPTIONS --type-in-type #-}

module Control.Optics.Profunctor where

open import Prelude

open import Data.Profunctor

private
  variable
    A B C R S T : Set
    F : Set -> Set
    P : Set -> Set -> Set

--------------------------------------------------------------------------------
-- Types classes for characterizing optics
--------------------------------------------------------------------------------

-- Characterizes Lens
record Strong (P : Set -> Set -> Set) : Set where
  field
    overlap {{super}} : Profunctor P
    strong : P A B -> P (C * A) (C * B)

open Strong {{...}} public

-- Characterizes Prism
record Choice (P : Set -> Set -> Set) : Set where
  field
    overlap {{super}} : Profunctor P
    choice : P A B -> P (C + A) (C + B)

open Choice {{...}} public

-- Characterizes Grate
record Closed (P : Set -> Set -> Set) : Set where
  field
    overlap {{super}} : Profunctor P
    closed : P A B -> P (C -> A) (C -> B)

open Closed {{...}} public

-- Characterizes Traversal
record Wander (P : Set -> Set -> Set) : Set where
  field
    overlap {{superStrong}} : Strong P
    overlap {{superChoice}} : Choice P
    wander : (forall {F} {{_ : Applicative F}} -> (A -> F B) -> S -> F T)
      -> P A B -> P S T

open Wander {{...}}

--------------------------------------------------------------------------------
-- Profunctor for characterizing optics
--------------------------------------------------------------------------------

-- Characterizes Fold
record Forget (R A B : Set) : Set where
  constructor toForget
  field
    fromForget : A -> R

open Forget

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

Fold : Set -> Optic
Fold R A B S T = Forget R A B -> Forget R S T

Getter : Optic
Getter A B S T = forall {R} -> Fold R A B S T

Review : (B T : Set) -> Set
Review B T = B -> T

Setter : Optic
Setter A B S T = (A -> B) -> S -> T

--------------------------------------------------------------------------------
-- Concrete optics
--------------------------------------------------------------------------------

-- Corresponds to Adapter
record Exchange (A B S T : Set) : Set where
  constructor toExchange
  field
    from : S -> A
    to : B -> T

-- Corresponds to Lens
record Shop (A B S T : Set) : Set where
  constructor toShop
  field
    get : S -> A
    put : S -> B -> T

-- Corresponds to Prism
record Market (A B S T : Set) : Set where
  constructor toMarket
  field
    build : B -> T
    match : S -> T + A

-- Corresponds to Grate
record Grating (A B S T : Set) : Set where
  constructor toGrating
  field
    degrating : ((S -> A) -> B) -> T

-- Corresponds to Traversal
record Bazaar (P : Set -> Set -> Set) (A B S T : Set) : Set where
  constructor toBazaar
  field
    traverseOf : {{_ : Applicative F}} -> P A (F B) -> S -> F T

-- Corresponds to Setter
record Mapping (A B S T : Set) : Set where
  constructor toMapping
  field
    mapOf : (A -> B) -> S -> T

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

adapter : (S -> A) -> (B -> T) -> Adapter A B S T
adapter from to = dimap from to

lens : (S -> A) -> (S -> B -> T) -> Lens A B S T
lens get put = dimap (split identity get) (uncurry put) <<< strong

prism : (B -> T) -> (S -> T + A) -> Prism A B S T
prism build match = dimap match untag <<< choice <<< rmap build

grate : (((S -> A) -> B) -> T) -> Grate A B S T
grate degrating = dimap (flip _$_) degrating <<< closed

traversal : (forall {F} {{_ : Applicative F}} -> (A -> F B) -> S -> F T)
  -> Traversal A B S T
traversal traverse = wander traverse

getter : (S -> A) -> Simple Getter A S
getter g f = toForget (g >>> fromForget f)

--------------------------------------------------------------------------------
-- Profunctor instances
--------------------------------------------------------------------------------

instance
  profunctorForget : Profunctor (Forget R)
  profunctorForget .dimap f g h = toForget (fromForget h <<< f)

  profunctorAdapter : Profunctor (Adapter A B)
  profunctorAdapter .dimap f g adapter = dimap f g <<< adapter

  profunctorExchange : Profunctor (Exchange A B)
  profunctorExchange .dimap f g (toExchange from to) =
    toExchange (from <<< f) (g <<< to)

  profunctorLens : Profunctor (Lens A B)
  profunctorLens .dimap f g lens = dimap f g <<< lens

  profunctorShop : Profunctor (Shop A B)
  profunctorShop .dimap f g (toShop get put) =
    toShop (get <<< f) (\ s -> g <<< put (f s))

  strongShop : Strong (Shop A B)
  strongShop .strong (toShop get put) = toShop get' put'
    where
      get' put' : _
      get' (u , s) = get s
      put' (u , s) y = (u , put s y)

  profunctorPrism : Profunctor (Prism A B)
  profunctorPrism .dimap f g prism = dimap f g <<< prism

  profunctorMarket : Profunctor (Market A B)
  profunctorMarket .dimap f g (toMarket build match) =
      toMarket (g <<< build) (first g <<< match <<< f)

  choiceMarket : Choice (Market A B)
  choiceMarket .choice (toMarket build match) = toMarket build' match'
    where
      build' match' : _
      build' y = right (build y)
      match' (left u) = left (left u)
      match' (right s) with match s
      ... | left t = left (right t)
      ... | right x = right x

  profunctorGrate : Profunctor (Grate A B)
  profunctorGrate .dimap f g grate = dimap f g <<< grate

  profunctorGrating : Profunctor (Grating A B)
  profunctorGrating .dimap f g (toGrating degrating) =
    toGrating \ d -> g (degrating \ k -> d (k <<< f))

  closedGrating : Closed (Grating A B)
  closedGrating .closed (toGrating degrating) =
    toGrating \ f x -> degrating \ k -> f \ g -> k (g x)

  profunctorTraversal : Profunctor (Traversal A B)
  profunctorTraversal .dimap f g traverse = dimap f g <<< traverse

  profunctorBazaar : Profunctor (Bazaar P A B)
  profunctorBazaar .dimap f g (toBazaar b) = toBazaar \ h s -> g <$> b h (f s)

  strongBazaar : Strong (Bazaar P A B)
  strongBazaar .strong (toBazaar b) = toBazaar \ where
    h (u , s) -> _,_ u <$> b h s

  choiceBazaar : Choice (Bazaar P A B)
  choiceBazaar .choice (toBazaar b) = toBazaar \ where
    h (right s) -> right <$> b h s
    h (left u) -> left <$> pure u

  wanderBazaar : Wander (Bazaar P A B)
  wanderBazaar .wander w (toBazaar b) = toBazaar \ where
    h s -> w (b h) s

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

from : Adapter A B S T -> S -> A
to : Adapter A B S T -> B -> T
from a = Exchange.from $ a $ toExchange identity identity
to a = Exchange.to $ a $ toExchange identity identity

get : Lens A B S T -> S -> A
put : Lens A B S T -> S -> B -> T
get l = Shop.get $ l $ toShop identity (flip const)
put l = Shop.put $ l $ toShop identity (flip const)

build : Prism A B S T -> B -> T
match : Prism A B S T -> S -> T + A
build p = Market.build $ p $ toMarket identity right
match p = Market.match $ p $ toMarket identity right

degrating : Grate A B S T -> ((S -> A) -> B) -> T
degrating g = Grating.degrating $ g $ toGrating \ f -> f identity

traverseOf : Traversal A B S T
  -> (forall {F} {{_ : Applicative F}} -> (A -> F B) -> S -> F T)
traverseOf {A} {B} t = Bazaar.traverseOf (t b)
  where
    b : Bazaar Function A B A B
    b = toBazaar identity

view : Simple Getter A S -> S -> A
view g = fromForget $ g (toForget identity)

review : Review B T -> B -> T
review = identity

over : Setter A B S T -> (A -> B) -> S -> T
over = identity
