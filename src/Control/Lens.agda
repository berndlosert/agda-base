{-# OPTIONS --type-in-type #-}

module Control.Lens where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Functor.Identity
open import Data.Functor.Const
open import Data.Monoid.All
open import Data.Monoid.Any
open import Data.Monoid.Dual
open import Data.Monoid.Endo
open import Data.Profunctor.Choice
open import Data.Semigroup.First
open import Data.Semigroup.Last

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Functor.Identity public
open Data.Functor.Const public
open Data.Monoid.All public
open Data.Monoid.Any public
open Data.Monoid.Dual public
open Data.Monoid.Endo public
open Data.Semigroup.First public
open Data.Semigroup.Last public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c r s t : Set
    f g m : Set -> Set

-------------------------------------------------------------------------------
-- Sets and type classes used for characterizing optics
-------------------------------------------------------------------------------

record Copointed (f : Set -> Set) : Set where
  field extract : f a -> a

open Copointed {{...}} public

instance
  Copointed-Identity : Copointed Identity
  Copointed-Identity .extract = runIdentity

record Tagged (s b : Set) : Set where
  constructor toTagged
  field unTagged : b

open Tagged public

instance
  Functor-Tagged : Functor (Tagged s)
  Functor-Tagged .map f (toTagged x) = toTagged (f x)

  Profunctor-Tagged : Profunctor Tagged
  Profunctor-Tagged .lcmap _ (toTagged x) = toTagged x

  Choice-Tagged : Choice Tagged
  Choice-Tagged .choicel (toTagged x) = toTagged (left x)

data Exchange (a b s t : Set) : Set where
  toExchange : (s -> a) -> (b -> t) -> Exchange a b s t

instance
  Functor-Exchange : Functor (Exchange a b s)
  Functor-Exchange .map f (toExchange sa bt) = toExchange sa (f <<< bt)

  Profunctor-Exchange : Profunctor (Exchange a b)
  Profunctor-Exchange .lcmap f (toExchange sa bt) = toExchange (sa <<< f) bt

data Market (a b s t : Set) : Set where
  toMarket : (b -> t) -> (s -> Either t a) -> Market a b s t

instance
  Functor-Market : Functor (Market a b s)
  Functor-Market .map f (toMarket bt seta) =
    toMarket (f <<< bt) (either (left <<< f) right <<< seta)

  Profunctor-Market : Profunctor (Market a b)
  Profunctor-Market .lcmap f (toMarket bt seta) = toMarket bt (seta <<< f)

  Choice-Market : Choice (Market a b)
  Choice-Market .choicel (toMarket bt seta) =
    toMarket (left <<< bt) \ where
      (left s) -> either (left <<< left) right (seta s)
      (right c) -> left (right c)

-------------------------------------------------------------------------------
-- Optic types ala Van Laarhoven
-------------------------------------------------------------------------------

Simple : (Set -> Set -> Set -> Set -> Set) -> Set -> Set -> Set
Simple Optic s a = Optic s s a a

Traversal : (s t a b : Set) -> Set
Traversal s t a b = forall {f} -> {{Applicative f}}
  -> (a -> f b) -> s -> f t

Setter : (s t a b : Set) -> Set
Setter s t a b = forall {f} -> {{Applicative f}} -> {{Copointed f}}
  -> (a -> f b) -> s -> f t

Fold : (s t a b : Set) -> Set
Fold s t a b = forall {f} -> {{Applicative f}} -> {{Contravariant f}}
  -> (a -> f b) -> s -> f t

Getter : (s t a b : Set) -> Set
Getter s t a b = forall {f} -> {{Functor f}} -> {{Contravariant f}}
  -> (a -> f b) -> s -> f t

Lens : (s t a b : Set) -> Set
Lens s t a b = forall {f} -> {{Functor f}}
  -> (a -> f b) -> s -> f t

Iso : (s t a b : Set) -> Set
Iso s t a b = forall {p} {f} -> {{Profunctor p}} -> {{Functor f}}
  -> p a (f b) -> p s (f t)

Prism : (s t a b : Set) -> Set
Prism s t a b = forall {p} {f} -> {{Choice p}} -> {{Applicative f}}
  -> p a (f b) -> p s (f t)

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

lens : (s -> a) -> (s -> b -> t) -> Lens s t a b
lens v u f s = map (u s) (f (v s))

prism : (b -> t)  -> (s -> Either t a) -> Prism s t a b
prism bt seta = dimap seta (either pure (map bt)) <<< choicer

prism' : (b -> s)  -> (s -> Maybe a) -> Prism s s a b
prism' bs sma = prism bs (\ s -> maybe (left s) right (sma s))

iso : (s -> a) -> (b -> t) -> Iso s t a b
iso f g = dimap f (map g)

-------------------------------------------------------------------------------
-- Getting operations
-------------------------------------------------------------------------------

Getting : (r s a : Set) -> Set
Getting r s a = (a -> Const r a) -> s -> Const r s

to : (s -> a) -> Getting r s a
to f k = toConst <<< getConst <<< k <<< f

view : Getting a s a -> s -> a
view g = getConst <<< g toConst

foldMapOf : Getting r s a -> (a -> r) -> s -> r
foldMapOf g k = getConst <<< g (toConst <<< k)

foldOf : Getting a s a -> s -> a
foldOf l = getConst <<< l toConst

foldrOf : Getting (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf l f z = flip appEndo z <<< foldMapOf l (toEndo <<< f)

foldlOf : Getting (Dual (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldlOf l f z =
  map (flip appEndo z <<< getDual) (foldMapOf l (toDual <<< toEndo <<< flip f))

foldlMOf : {{Monad m}} -> Getting (Endo (r -> m r)) s a
  -> (r -> a -> m r) -> r -> s -> m r
foldlMOf l f z0 xs = foldrOf l (\ x k z -> f z x >>= k) pure xs z0

toListOf : Getting (Endo (List a)) s a -> s -> List a
toListOf l = foldrOf l _::_ []

has : Getting Any s a -> s -> Bool
has l = getAny <<< foldMapOf l (\ _ -> toAny true)

hasn't : Getting All s a -> s -> Bool
hasn't l = getAll <<< foldMapOf l (\ _ -> toAll false)

lengthOf : Getting (Dual (Endo Nat)) s a -> s -> Nat
lengthOf l = foldlOf l (\ n _ -> suc n) zero

preview : Getting (Maybe (First a)) s a -> s -> Maybe a
preview l = map getFirst <<< foldMapOf l (just <<< toFirst)

firstOf : Getting (First a) s a -> s -> a
firstOf l = getFirst <<< foldMapOf l toFirst

lastOf : Getting (Last a) s a -> s -> a
lastOf l = getLast <<< foldMapOf l toLast

findOf : Getting (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf l p = foldrOf l (\ x y -> if p x then just x else y) nothing

traverseOf! : {{Functor f}}
  -> Getting (f r) s a -> (a -> f r) -> s -> f Unit
traverseOf! l f = map (const tt) <<< foldMapOf l f

forOf! : {{Functor f}}
  -> Getting (f r) s a -> s -> (a -> f r) -> f Unit
forOf! = flip <<< traverseOf!

-------------------------------------------------------------------------------
-- ASetter
-------------------------------------------------------------------------------

ASetter : (s t a b : Set) -> Set
ASetter s t a b = (a -> Identity b) -> s -> Identity t

over : ASetter s t a b -> (a -> b) -> s -> t
over g k = runIdentity <<< g (toIdentity <<< k)

set : ASetter s t a b -> b -> s -> t
set f b = runIdentity <<< f (\ _ -> toIdentity b)

sets : ((a -> b) -> s -> t) -> ASetter s t a b
sets f k = toIdentity <<< f (runIdentity <<< k)

-------------------------------------------------------------------------------
-- AReview
-------------------------------------------------------------------------------

AReview : (t b : Set) -> Set
AReview t b = Tagged b (Identity b) -> Tagged t (Identity t)

review : AReview t b -> b -> t
review p = runIdentity <<< unTagged <<< p <<< toTagged <<< toIdentity

-------------------------------------------------------------------------------
-- AnIso
-------------------------------------------------------------------------------

AnIso : (s t a b : Set) -> Set
AnIso s t a b = Exchange a b a (Identity b) -> Exchange a b s (Identity t)

withIso : AnIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso ai k =
  case ai (toExchange id toIdentity) of \ where
    (toExchange sa bt) -> k sa (runIdentity <<< bt)

under : AnIso s t a b -> (t -> s) -> b -> a
under ai = withIso ai \ sa bt ts -> sa <<< ts <<< bt

mapping : {{Functor f}} -> {{Functor g}}
  -> AnIso s t a b -> Iso (f s) (g t) (f a) (g b)
mapping k = withIso k $ \ sa bt -> iso (map sa) (map bt)

-------------------------------------------------------------------------------
-- APrism
-------------------------------------------------------------------------------

APrism : (s t a b : Set) -> Set
APrism s t a b = Market a b a (Identity b) -> Market a b s (Identity t)

withPrism : APrism s t a b -> ((b -> t) -> (s -> Either t a) -> r) -> r
withPrism ap f =
  case ap (toMarket toIdentity right) of \ where
    (toMarket bt seta) ->
      f (runIdentity <<< bt) (either (left <<< runIdentity) right <<< seta)

matching : APrism s t a b -> s -> Either t a
matching ap = withPrism ap \ _ seta -> seta

isn't : APrism s t a b -> s -> Bool
isn't ap s = either (const true) (const false) (matching ap s)

is : APrism s t a b -> s -> Bool
is ap = not <<< isn't ap

-------------------------------------------------------------------------------
-- Some general optics
-------------------------------------------------------------------------------

mapped : {{Functor f}} -> ASetter (f a) (f b) a b
mapped = sets map

record Folded (s a : Set) : Set where
  field folded : {{Monoid r}} -> Getting r s a

open Folded {{...}} public

instance
  Folded-List : Folded (List a) a
  Folded-List .folded f [] = neutral
  Folded-List .folded f (x :: xs) = toConst (getConst $ f x) <> folded f xs

record Each (s t a b : Set) : Set where
  field each : Traversal s t a b

open Each {{...}} public

instance
  Each-Pair : Each (Pair a a) (Pair b b) a b
  Each-Pair .each f (a , b) = (| _,_ (f a) (f b) |)

  Each-Maybe : Each (Maybe a) (Maybe b) a b
  Each-Maybe .each f nothing = pure nothing
  Each-Maybe .each f (just x) = map pure (f x)

  Each-Either : Each (Either a a) (Either b b) a b
  Each-Either .each f (left a) = map left (f a)
  Each-Either .each f (right a) = map right (f a)

  Each-List : Each (List a) (List b) a b
  Each-List .each f [] = pure []
  Each-List .each f (x :: xs) = (| _::_ (f x) (each f xs) |)

record Cons (s t a b : Set) : Set where
  field #Cons : Prism s t (Pair a s) (Pair b t)

open Cons {{...}} public

instance
  Cons-List : Cons (List a) (List b) a b
  Cons-List .#Cons = prism (uncurry _::_) \ where
    (a :: as) -> right (a , as)
    [] -> left []

-------------------------------------------------------------------------------
-- Some specific optics
-------------------------------------------------------------------------------

#fst : Lens (Pair a c) (Pair b c) a b
#fst k (a , c) = map (_, c) (k a)

#snd : Lens (Pair a b) (Pair a c) b c
#snd k (x , y) = map (x ,_) (k y)

#Left : Traversal (Either a c) (Either b c) a b
#Left f (left x) = map left (f x)
#Left _ (right y) = pure (right y)

#Right : Traversal (Either a b) (Either a c) b c
#Right f (right y) = map right (f y)
#Right _ (left x) = pure (left x)

#Just : Traversal (Maybe a) (Maybe b) a b
#Just f (just x) = map just (f x)
#Just _ nothing = pure nothing

#nothing : Simple Traversal (Maybe a) Unit
#nothing f nothing = map (const nothing) (f tt)
#nothing _ j = pure j

#head : {{Cons s s a a}} -> Simple Traversal s a
#head = #Cons <<< #fst

#tail : {{Cons s s a a}} -> Simple Traversal s s
#tail = #Cons <<< #snd
