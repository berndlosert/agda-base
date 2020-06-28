{-# OPTIONS --type-in-type #-}

module Control.Optics.Profunctor where

open import Prelude

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
-- Profunctors for characterizing optics
--------------------------------------------------------------------------------

-- Characterizes Fold
record Forget (R A B : Set) : Set where
  constructor forget:
  field runForget : A -> R

open Forget

-- Characaterizes Review
record Tagged (A B : Set) : Set where
  constructor tagged:
  field unTagged : B

open Tagged

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

Review : Optic
Review A B S T = Tagged A B -> Tagged S T

Setter : Optic
Setter A B S T = Function A B -> Function S T

--------------------------------------------------------------------------------
-- Concrete optics
--------------------------------------------------------------------------------

-- Corresponds to Adapter
record Exchange (A B S T : Set) : Set where
  constructor exchange:
  field
    from : S -> A
    to : B -> T

-- Corresponds to Lens
record Shop (A B S T : Set) : Set where
  constructor shop:
  field
    get : S -> A
    put : S -> B -> T

-- Corresponds to Prism
record Market (A B S T : Set) : Set where
  constructor market:
  field
    build : B -> T
    match : S -> T + A

-- Corresponds to Grate
record Grating (A B S T : Set) : Set where
  constructor grate:
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
lens get put = dimap (split id get) (uncurry put) ∘ strong

prism : (B -> T) -> (S -> T + A) -> Prism A B S T
prism build match = dimap match untag ∘ choice ∘ rmap build

grate : (((S -> A) -> B) -> T) -> Grate A B S T
grate degrating = dimap (flip _$_) degrating ∘ closed

traversal : (forall {F} {{_ : Applicative F}} -> (A -> F B) -> S -> F T)
  -> Traversal A B S T
traversal traverse = wander traverse

getter : (S -> A) -> Simple Getter A S
getter g f = forget: (runForget f ∘ g)

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance
  profunctorForget : Profunctor (Forget R)
  profunctorForget .dimap f g h = forget: (runForget h ∘ f)

  strongForget : Strong (Forget R)
  strongForget .strong z = forget: (runForget z ∘ snd)

  choiceForget : {{_ : Monoid R}} -> Choice (Forget R)
  choiceForget .choice z = forget: $ either neutral (runForget z)

  wanderForget : {{_ : Monoid R}} -> Wander (Forget R)
  wanderForget .wander t f =
    forget: $ getConst ∘ t (const: ∘ runForget f)

  profunctorTagged : Profunctor Tagged
  profunctorTagged .dimap _ g x = tagged: (g $ unTagged x)

  choiceTagged : Choice Tagged
  choiceTagged .choice x = tagged: (right $ unTagged x)

  closedTagged : Closed Tagged
  closedTagged .closed x = tagged: (const $ unTagged x)

  profunctorAdapter : Profunctor (Adapter A B)
  profunctorAdapter .dimap f g a = dimap f g ∘ a

  profunctorExchange : Profunctor (Exchange A B)
  profunctorExchange .dimap f g (exchange: from to) =
    exchange: (from ∘ f) (g ∘ to)

  profunctorLens : Profunctor (Lens A B)
  profunctorLens .dimap f g l = dimap f g ∘ l

  profunctorShop : Profunctor (Shop A B)
  profunctorShop .dimap f g (shop: get put) =
    shop: (get ∘ f) (\ s -> g ∘ put (f s))

  strongShop : Strong (Shop A B)
  strongShop .strong (shop: get put) = shop: get' put'
    where
      get' put' : _
      get' (u , s) = get s
      put' (u , s) y = (u , put s y)

  profunctorPrism : Profunctor (Prism A B)
  profunctorPrism .dimap f g p = dimap f g ∘ p

  profunctorMarket : Profunctor (Market A B)
  profunctorMarket .dimap f g (market: build match) =
      market: (g ∘ build) (first g ∘ match ∘ f)

  choiceMarket : Choice (Market A B)
  choiceMarket .choice (market: build match) = market: build' match'
    where
      build' match' : _
      build' y = right (build y)
      match' (left u) = left (left u)
      match' (right s) with match s
      ... | left t = left (right t)
      ... | right x = right x

  profunctorGrate : Profunctor (Grate A B)
  profunctorGrate .dimap f g r = dimap f g ∘ r

  profunctorGrating : Profunctor (Grating A B)
  profunctorGrating .dimap f g (grate: r) =
    grate: \ d -> g (r \ k -> d (k ∘ f))

  closedGrating : Closed (Grating A B)
  closedGrating .closed (grate: degrating) =
    grate: \ f x -> degrating \ k -> f \ g -> k (g x)

  profunctorTraversal : Profunctor (Traversal A B)
  profunctorTraversal .dimap f g t = dimap f g ∘ t

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

  profunctorSetter : Profunctor (Setter A B)
  profunctorSetter .dimap f g h k = g ∘ h k ∘ f

  strongSetter : Strong (Setter A B)
  strongSetter .strong f g (c , a) = (c , f g a)

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

--from : Adapter A B S T -> S -> A
--from a = Exchange.from $ a $ exchange: id id
--to : Adapter A B S T -> B -> T
--to a = Exchange.to $ a $ exchange: id id

--get : Lens A B S T -> S -> A
--get l = Shop.get $ l $ shop: id (flip const)
--put : Lens A B S T -> S -> B -> T
--put l = Shop.put $ l $ shop: id (flip const)

--build : Prism A B S T -> B -> T
--build p = Market.build $ p $ market: id right
--match : Prism A B S T -> S -> T + A
--match p = Market.match $ p $ market: id right

--degrating : Grate A B S T -> ((S -> A) -> B) -> T
--degrating g = Grating.degrating $ g $ grate: \ f -> f id

traverseOf : Traversal A B S T
  -> (forall {F} {{_ : Applicative F}} -> (A -> F B) -> S -> F T)
traverseOf {A} {B} t = Bazaar.traverseOf (t b)
  where
    b : Bazaar Function A B A B
    b = toBazaar id

to : (S -> A) -> Getter A B S T
to f (forget: g) = forget: (g ∘ f)

view : Getter A B S T -> S -> A
view g = runForget $ g (forget: id)

foldMapOf : Getter A B S T -> (A -> R) -> S -> R
foldMapOf g f = runForget $ g (forget: f)

review : Review A B S T -> B -> T
review r b = unTagged $ r (tagged: b)

over : Setter A B S T -> (A -> B) -> S -> T
over = id

set : Setter A B S T -> B -> S -> T
set f b = f (const b)

sets : ((A -> B) -> S -> T) -> Setter A B S T
sets = id

--------------------------------------------------------------------------------
-- Basic lens and traversals
--------------------------------------------------------------------------------

--#fst : Lens A B (A * C) (B * C)
--  -- : P A B -> P (A * C) (B * C)
--#fst =

--#snd : Lens B C (A * B) (A * C)
#snd : Simple Lens B (A * B)
#snd = strong
--
--#left : Traversal (A + C) (B + C) A B
--#left f (left x) = left <$> f x
--#left _ (right y) = pure (right y)
--
--#right : Traversal (A + B) (A + C) B C
--#right f (right y) = right <$> f y
--#right _ (left x) = pure (left x)
--
--#just : Traversal (Maybe A) (Maybe B) A B
--#just f (just x) = just <$> f x
--#just _ nothing = pure nothing
--
--#nothing : Simple Traversal (Maybe A) Unit
--#nothing f nothing = const nothing <$> f unit
--#nothing _ j = pure j
