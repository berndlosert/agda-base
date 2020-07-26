module Control.Optics.Profunctor where

open import Prelude

private
  variable
    a b c r s t : Set
    f : Set -> Set
    p : Set -> Set -> Set

--------------------------------------------------------------------------------
-- Types classes for characterizing optics
--------------------------------------------------------------------------------

-- Characterizes Lens
record Strong (p : Set -> Set -> Set) : Set where
  field
    overlap {{super}} : Profunctor p
    strong : p a b -> p (c * a) (c * b)

open Strong {{...}} public

-- Characterizes Prism
record Choice (p : Set -> Set -> Set) : Set where
  field
    overlap {{super}} : Profunctor p
    choice : p a b -> p (c + a) (c + b)

open Choice {{...}} public

-- Characterizes Grate
record Closed (p : Set -> Set -> Set) : Set where
  field
    overlap {{super}} : Profunctor p
    closed : p a b -> p (c -> a) (c -> b)

open Closed {{...}} public

-- Characterizes traversal
record Wander (p : Set -> Set -> Set) : Set where
  field
    overlap {{superStrong}} : Strong p
    overlap {{superChoice}} : Choice p
    wander : (forall {f} {{_ : Applicative f}} -> (a -> f b) -> s -> f t)
      -> p a b -> p s t

open Wander {{...}}

--------------------------------------------------------------------------------
-- Profunctors for characterizing optics
--------------------------------------------------------------------------------

-- Characterizes Fold
record Forget (r a b : Set) : Set where
  constructor Forget:
  field runForget : a -> r

open Forget

-- Characaterizes Review
record Tagged (a b : Set) : Set where
  constructor Tagged:
  field unTagged : b

open Tagged

--------------------------------------------------------------------------------
-- Profunctor optics
--------------------------------------------------------------------------------

Optic : Set
Optic = (a b s t : Set) -> Set

Simple : Optic -> Set -> Set -> Set
Simple o a s = o a a s s

Adapter : Optic
Adapter a b s t = forall {p} {{_ : Profunctor p}} -> p a b -> p s t

Lens : Optic
Lens a b s t = forall {p} {{_ : Strong p}} -> p a b -> p s t

Prism : Optic
Prism a b s t = forall {p} {{_ : Choice p}} -> p a b -> p s t

Grate : Optic
Grate a b s t = forall {p} {{_ : Closed p}} -> p a b -> p s t

Traversal : Optic
Traversal a b s t = forall {p} {{_ : Wander p}} -> p a b -> p s t

Fold : Set -> Optic
Fold r a b s t = Forget r a b -> Forget r s t

Getter : Optic
Getter a b s t = forall {r} -> Fold r a b s t

Review : Optic
Review a b s t = Tagged a b -> Tagged s t

Setter : Optic
Setter a b s t = Function a b -> Function s t

--------------------------------------------------------------------------------
-- Concrete optics
--------------------------------------------------------------------------------

-- Corresponds to Adapter
record Exchange (a b s t : Set) : Set where
  constructor Exchange:
  field
    from : s -> a
    to : b -> t

-- Corresponds to Lens
record Shop (a b s t : Set) : Set where
  constructor Shop:
  field
    get : s -> a
    put : s -> b -> t

-- Corresponds to Prism
record Market (a b s t : Set) : Set where
  constructor Market:
  field
    build : b -> t
    match : s -> t + a

-- Corresponds to Grate
record Grating (a b s t : Set) : Set where
  constructor Grate:
  field
    degrating : ((s -> a) -> b) -> t

-- Corresponds to Traversal
record Bazaar (p : Set -> Set -> Set) (a b s t : Set) : Set where
  constructor Bazaar:
  field
    traverseOf : {{_ : Applicative f}} -> p a (f b) -> s -> f t

-- Corresponds to Setter
record Mapping (a b s t : Set) : Set where
  constructor Mapping:
  field
    mapOf : (a -> b) -> s -> t

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

adapter : (s -> a) -> (b -> t) -> Adapter a b s t
adapter from to = dimap from to

lens : (s -> a) -> (s -> b -> t) -> Lens a b s t
lens get put = dimap (tuple id get) (uncurry put) ∘ strong

prism : (b -> t) -> (s -> t + a) -> Prism a b s t
prism build match = dimap match untag ∘ choice ∘ rmap build

grate : (((s -> a) -> b) -> t) -> Grate a b s t
grate degrating = dimap (flip _$_) degrating ∘ closed

traversal : (forall {f} {{_ : Applicative f}} -> (a -> f b) -> s -> f t)
  -> Traversal a b s t
traversal traverse = wander traverse

getter : (s -> a) -> Simple Getter a s
getter g f = Forget: (runForget f ∘ g)

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance
  profunctorForget : Profunctor (Forget r)
  profunctorForget .dimap f g h = Forget: (runForget h ∘ f)

  strongForget : Strong (Forget r)
  strongForget .strong z = Forget: (runForget z ∘ snd)

  choiceForget : {{_ : Monoid r}} -> Choice (Forget r)
  choiceForget .choice z = Forget: $ either neutral (runForget z)

  wanderForget : {{_ : Monoid r}} -> Wander (Forget r)
  wanderForget .wander t f =
    Forget: $ getConst ∘ t (Const: ∘ runForget f)

  profunctorTagged : Profunctor Tagged
  profunctorTagged .dimap _ g x = Tagged: (g $ unTagged x)

  choiceTagged : Choice Tagged
  choiceTagged .choice x = Tagged: (Right $ unTagged x)

  closedTagged : Closed Tagged
  closedTagged .closed x = Tagged: (const $ unTagged x)

  profunctorAdapter : Profunctor (Adapter a b)
  profunctorAdapter .dimap f g a = dimap f g ∘ a

  profunctorExchange : Profunctor (Exchange a b)
  profunctorExchange .dimap f g (Exchange: from to) =
    Exchange: (from ∘ f) (g ∘ to)

  profunctorLens : Profunctor (Lens a b)
  profunctorLens .dimap f g l = dimap f g ∘ l

  profunctorShop : Profunctor (Shop a b)
  profunctorShop .dimap f g (Shop: get put) =
    Shop: (get ∘ f) (λ s -> g ∘ put (f s))

  strongShop : Strong (Shop a b)
  strongShop .strong (Shop: get put) = Shop: get' put'
    where
      get' put' : _
      get' (u , s) = get s
      put' (u , s) y = (u , put s y)

  profunctorPrism : Profunctor (Prism a b)
  profunctorPrism .dimap f g p = dimap f g ∘ p

  profunctorMarket : Profunctor (Market a b)
  profunctorMarket .dimap f g (Market: build match) =
      Market: (g ∘ build) (first g ∘ match ∘ f)

  choiceMarket : Choice (Market a b)
  choiceMarket .choice (Market: build match) = Market: build' match'
    where
      build' match' : _
      build' y = Right (build y)
      match' (Left u) = Left (Left u)
      match' (Right s) with match s
      ... | Left t = Left (Right t)
      ... | Right x = Right x

  profunctorGrate : Profunctor (Grate a b)
  profunctorGrate .dimap f g r = dimap f g ∘ r

  profunctorGrating : Profunctor (Grating a b)
  profunctorGrating .dimap f g (Grate: r) =
    Grate: λ d -> g (r λ k -> d (k ∘ f))

  closedGrating : Closed (Grating a b)
  closedGrating .closed (Grate: degrating) =
    Grate: λ f x -> degrating λ k -> f λ g -> k (g x)

  profunctorTraversal : Profunctor (Traversal a b)
  profunctorTraversal .dimap f g t = dimap f g ∘ t

  profunctorBazaar : Profunctor (Bazaar p a b)
  profunctorBazaar .dimap f g (Bazaar: b) = Bazaar: λ h s -> g <$> b h (f s)

  strongBazaar : Strong (Bazaar p a b)
  strongBazaar .strong (Bazaar: b) = Bazaar: λ where
    h (u , s) -> _,_ u <$> b h s

  choiceBazaar : Choice (Bazaar p a b)
  choiceBazaar .choice (Bazaar: b) = Bazaar: λ where
    h (Right s) -> Right <$> b h s
    h (Left u) -> Left <$> pure u

  wanderBazaar : Wander (Bazaar p a b)
  wanderBazaar .wander w (Bazaar: b) = Bazaar: λ where
    h s -> w (b h) s

  profunctorSetter : Profunctor (Setter a b)
  profunctorSetter .dimap f g h k = g ∘ h k ∘ f

  strongSetter : Strong (Setter a b)
  strongSetter .strong f g (c , a) = (c , f g a)

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

--from : Adapter a b s t -> s -> a
--from a = Exchange.from $ a $ Exchange: id id
--to : Adapter a b s t -> b -> t
--to a = Exchange.to $ a $ Exchange: id id

--get : Lens a b s t -> s -> a
--get l = Shop.get $ l $ Shop: id (flip const)
--put : Lens a b s t -> s -> b -> t
--put l = Shop.put $ l $ Shop: id (flip const)

--build : Prism a b s t -> b -> t
--build p = Market.build $ p $ Market: id Right
--match : Prism a b s t -> s -> t + A
--match p = Market.match $ p $ Market: id Right

--degrating : Grate a b s t -> ((s -> a) -> b) -> t
--degrating g = Grating.degrating $ g $ Grate: λ f -> f id

traverseOf : Traversal a b s t
  -> (forall {f} {{_ : Applicative f}} -> (a -> f b) -> s -> f t)
traverseOf {a} {b} t = Bazaar.traverseOf (t x)
  where
    x : Bazaar Function a b a b
    x = Bazaar: id

to : (s -> a) -> Getter a b s t
to f (Forget: g) = Forget: (g ∘ f)

view : Getter a b s t -> s -> a
view g = runForget $ g (Forget: id)

foldMapOf : Getter a b s t -> (a -> r) -> s -> r
foldMapOf g f = runForget $ g (Forget: f)

review : Review a b s t -> b -> t
review r b = unTagged $ r (Tagged: b)

over : Setter a b s t -> (a -> b) -> s -> t
over = id

set : Setter a b s t -> b -> s -> t
set f b = f (const b)

sets : ((a -> b) -> s -> t) -> Setter a b s t
sets = id

--------------------------------------------------------------------------------
-- Basic lens and traversals
--------------------------------------------------------------------------------

--#fst : Lens a b (a * c) (b * c)
--  -- : p a b -> p (a * c) (b * c)
--#fst =

#snd : Lens b c (a * b) (a * c)
--#snd : Simple Lens b (a * b)
#snd = strong
--
--#Left : Traversal (a + c) (b + c) a b
--#Left f (Left x) = Left <$> f x
--#Left _ (Right y) = pure (Right y)
--
--#Right : Traversal (a + b) (a + c) b C
--#Right f (Right y) = Right <$> f y
--#Right _ (Left x) = pure (Left x)
--
--#Just : Traversal (Maybe a) (Maybe b) a b
--#Just f (Just x) = Just <$> f x
--#Just _ Nothing = pure Nothing
--
--#Nothing : Simple Traversal (Maybe a) Unit
--#Nothing f Nothing = const Nothing <$> f unit
--#Nothing _ j = pure j
