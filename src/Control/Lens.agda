{-# OPTIONS --type-in-type #-}

module Control.Lens where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Monoid.Dual
open import Data.Monoid.Endo
open import Data.Semigroup.First
open import Data.Semigroup.Last
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c r s t : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Types and type classes used for characterizing optics
-------------------------------------------------------------------------------

record Copointed (f : Set -> Set) : Set where
  field extract : f a -> a

open Copointed {{...}} public

instance
  Copointed-Identity : Copointed Identity
  Copointed-Identity .extract = runIdentity

record Choice (p : Set -> Set -> Set) : Set where
  field
    {{super}} : Profunctor p
    lchoice : p a b -> p (a + c) (b + c)

  rchoice : p a b -> p (c + a) (c + b)
  rchoice = dimap (either Right Left) (either Right Left) <<< lchoice

open Choice {{...}} public

instance
  Choice-Function : Choice Function
  Choice-Function .lchoice ab (Left a) = Left (ab a)
  Choice-Function .lchoice _ (Right c) = Right c

record Tagged (s b : Set) : Set where
  constructor Tagged:
  field unTagged : b

open Tagged public

instance
  Profunctor-Tagged : Profunctor Tagged
  Profunctor-Tagged .dimap _ f (Tagged: x) = Tagged: (f x)

  Choice-Tagged : Choice Tagged
  Choice-Tagged .lchoice (Tagged: x) = Tagged: (Left x)

data Exchange (a b s t : Set) : Set where
  Exchange: : (s -> a) -> (b -> t) -> Exchange a b s t

instance
  Functor-Exchange : Functor (Exchange a b s)
  Functor-Exchange .map f (Exchange: sa bt) = Exchange: sa (f <<< bt)

  Profunctor-Exchange : Profunctor (Exchange a b)
  Profunctor-Exchange .dimap f g (Exchange: sa bt) =
    Exchange: (sa <<< f) (g <<< bt)

data Market (a b s t : Set) : Set where
  Market: : (b -> t) -> (s -> t + a) -> Market a b s t

instance
  Functor-Market : Functor (Market a b s)
  Functor-Market .map f (Market: bt seta) =
    Market: (f <<< bt) (either (Left <<< f) Right <<< seta)

  Profunctor-Market : Profunctor (Market a b)
  Profunctor-Market .dimap f g (Market: bt seta) =
    Market: (g <<< bt) (either (Left <<< g) Right <<< seta <<< f)

  Choice-Market : Choice (Market a b)
  Choice-Market .lchoice (Market: bt seta) =
    Market: (Left <<< bt) $ \ where
      (Left s) -> case seta s of \ where
        (Left t) -> Left (Left t)
        (Right a) -> Right a
      (Right c) -> Left (Right c)

-------------------------------------------------------------------------------
-- Optic types ala Van Laarhoven
-------------------------------------------------------------------------------

Simple : (Set -> Set -> Set -> Set -> Set) -> Set -> Set -> Set
Simple Optic s a = Optic s s a a

Traversal : (s t a b : Set) -> Set
Traversal s t a b = forall {f} {{_ : Applicative f}}
  -> (a -> f b) -> s -> f t

Setter : (s t a b : Set) -> Set
Setter s t a b = forall {f} {{_ : Applicative f}} {{_ : Copointed f}}
  -> (a -> f b) -> s -> f t

Fold : (s t a b : Set) -> Set
Fold s t a b = forall {f} {{_ : Applicative f}} {{_ : Contravariant f}}
  -> (a -> f b) -> s -> f t

Getter : (s t a b : Set) -> Set
Getter s t a b = forall {f} {{_ : Functor f}} {{_ : Contravariant f}}
  -> (a -> f b) -> s -> f t

Lens : (s t a b : Set) -> Set
Lens s t a b = forall {f} {{_ : Functor f}}
  -> (a -> f b) -> s -> f t

Iso : (s t a b : Set) -> Set
Iso s t a b = forall {p} {{_ : Profunctor p}} {f} {{_ : Functor f}}
  -> p a (f b) -> p s (f t)

Prism : (s t a b : Set) -> Set
Prism s t a b = forall {p} {{_ : Choice p}} {f} {{_ : Applicative f}}
  -> p a (f b) -> p s (f t)

-------------------------------------------------------------------------------
-- Getting operations
-------------------------------------------------------------------------------

Getting : (r s a : Set) -> Set
Getting r s a = (a -> Const r a) -> s -> Const r s

to : (s -> a) -> Getting r s a
to f k = Const: <<< getConst <<< k <<< f

view : Getting a s a -> s -> a
view g = getConst <<< g Const:

foldMapOf : Getting r s a -> (a -> r) -> s -> r
foldMapOf g k = getConst <<< g (Const: <<< k)

foldOf : Getting a s a -> s -> a
foldOf l = getConst <<< l Const:

foldrOf : Getting (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf l f z = flip appEndo z <<< foldMapOf l (Endo: <<< f)

foldlOf : Getting (Dual (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldlOf l f z = rmap (flip appEndo z <<< getDual) (foldMapOf l (Dual: <<< Endo: <<< flip f))

toListOf : Getting (Endo (List a)) s a -> s -> List a
toListOf l = foldrOf l _::_ []

countOf : Getting (Dual (Endo Nat)) s a -> s -> Nat
countOf l = foldlOf l (\ n _ -> Suc n) 0

preview : Getting (Maybe (First a)) s a -> s -> Maybe a
preview l = map getFirst <<< foldMapOf l (Just <<< First:)

firstOf : Getting (First a) s a -> s -> a
firstOf l = getFirst <<< foldMapOf l First:

lastOf : Getting (Last a) s a -> s -> a
lastOf l = getLast <<< foldMapOf l Last:

traverseOf! : {{_ : Functor f}}
  -> Getting (f r) s a -> (a -> f r) -> s -> f Unit
traverseOf! l f = map (const unit) <<< foldMapOf l f

forOf! : {{_ : Functor f}}
  -> Getting (f r) s a -> s -> (a -> f r) -> f Unit
forOf! = flip <<< traverseOf!

-------------------------------------------------------------------------------
-- ASetter
-------------------------------------------------------------------------------

ASetter : (s t a b : Set) -> Set
ASetter s t a b = (a -> Identity b) -> s -> Identity t

over : ASetter s t a b -> (a -> b) -> s -> t
over g k = runIdentity <<< g (Identity: <<< k)

set : ASetter s t a b -> b -> s -> t
set f b = runIdentity <<< f (\ _ -> Identity: b)

sets : ((a -> b) -> s -> t) -> ASetter s t a b
sets f k = Identity: <<< f (runIdentity <<< k)

-------------------------------------------------------------------------------
-- AReview
-------------------------------------------------------------------------------

AReview : (t b : Set) -> Set
AReview t b = Tagged b (Identity b) -> Tagged t (Identity t)

review : AReview t b -> b -> t
review p = runIdentity <<< unTagged <<< p <<< Tagged: <<< Identity:

-------------------------------------------------------------------------------
-- AnIso
-------------------------------------------------------------------------------

AnIso : (s t a b : Set) -> Set
AnIso s t a b = Exchange a b a (Identity b) -> Exchange a b s (Identity t)

withIso : AnIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso ai k with ai (Exchange: id Identity:)
... | Exchange: sa bt = k sa (runIdentity <<< bt)

under : AnIso s t a b -> (t -> s) -> b -> a
under ai = withIso ai \ sa bt ts -> sa <<< ts <<< bt

-------------------------------------------------------------------------------
-- APrism
-------------------------------------------------------------------------------

APrism : (s t a b : Set) -> Set
APrism s t a b = Market a b a (Identity b) -> Market a b s (Identity t)

withPrism : APrism s t a b -> ((b -> t) -> (s -> t + a) -> r) -> r
withPrism ap f with ap (Market: Identity: Right)
... | Market: bt seta =
  f (runIdentity <<< bt) (either (Left <<< runIdentity) Right <<< seta)

matching : APrism s t a b -> s -> t + a
matching ap = withPrism ap \ _ seta -> seta

isn't : APrism s t a b -> s -> Bool
isn't ap s with matching ap s
... | Left _ = True
... | Right _ = False

is : APrism s t a b -> s -> Bool
is ap = not <<< isn't ap

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

lens : (s -> a) -> (s -> b -> t) -> Lens s t a b
lens v u f s = map (u s) (f (v s))

prism : (b -> t)  -> (s -> t + a) -> Prism s t a b
prism bt seta = dimap seta (either pure (map bt)) <<< rchoice

prism' : (b -> s)  -> (s -> Maybe a) -> Prism s s a b
prism' bs sma = prism bs (\ s -> maybe (Left s) Right (sma s))

iso : (s -> a) -> (b -> t) -> Iso s t a b
iso f g = dimap f (map g)

-------------------------------------------------------------------------------
-- Some general optics
-------------------------------------------------------------------------------

packed : {{_ : Packed s a}} -> Simple Iso (List a) s
packed = iso pack unpack

unpacked : {{_ : Packed s a}} -> Simple Iso s (List a)
unpacked = iso unpack pack

mapped : {{_ : Functor f}} -> ASetter (f a) (f b) a b
mapped = sets map

folded : {{_ : Foldable f}} {{_ : Monoid r}} -> Getting r (f a) a
folded = foldring foldr
  where
    noEffect : {{_ : Monoid r}} -> Const r a
    noEffect = phantom (pure unit)

    foldring : {{_ : Monoid r}}
      -> ((a -> Const r a -> Const r a) -> Const r a -> s -> Const r a)
      -> (a -> Const r b) -> s -> Const r t
    foldring fr f = phantom <<< fr (\ a fa -> f a *> fa) noEffect

traversed : {{_ : Traversable f}} -> Traversal (f a) (f b) a b
traversed = traverse

record Each (s t a b : Set) : Set where
  field each : Traversal s t a b

open Each {{...}} public

instance
  Each-Tuple : Each (a * a) (b * b) a b
  Each-Tuple .each f (a , b) = (| _,_ (f a) (f b) |)

  Each-Maybe : Each (Maybe a) (Maybe b) a b
  Each-Maybe .each = traverse

  Each-Either : Each (Either a a) (Either b b) a b
  Each-Either .each f (Left a) = map Left (f a)
  Each-Either .each f (Right a) = map Right (f a)

  Each-List : Each (List a) (List b) a b
  Each-List .each = traverse

-------------------------------------------------------------------------------
-- Some specific optics
-------------------------------------------------------------------------------

#fst : Lens (a * c) (b * c) a b
#fst k (a , c) = map (_, c) (k a)

#snd : Lens (a * b) (a * c) b c
#snd k (x , y) = map (x ,_) (k y)

#Left : Traversal (a + c) (b + c) a b
#Left f (Left x) = map Left (f x)
#Left _ (Right y) = pure (Right y)

#Right : Traversal (a + b) (a + c) b c
#Right f (Right y) = map Right (f y)
#Right _ (Left x) = pure (Left x)

#Just : Traversal (Maybe a) (Maybe b) a b
#Just f (Just x) = map Just (f x)
#Just _ Nothing = pure Nothing

#Nothing : Simple Traversal (Maybe a) Unit
#Nothing f Nothing = map (const Nothing) (f unit)
#Nothing _ j = pure j
