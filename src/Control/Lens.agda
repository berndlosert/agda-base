{-# OPTIONS --type-in-type #-}

module Control.Lens where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Functor.Identity
open import Data.Functor.Const
open import Data.List as List using ()
open import Data.Monoid.Dual
open import Data.Monoid.Endo
open import Data.Profunctor.Choice
open import Data.Semigroup.First
open import Data.Semigroup.Last
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c r s t : Type
    f g : Type -> Type

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Functor.Identity public
open Data.Functor.Const public
open Data.Semigroup.First public
open Data.Semigroup.Last public

-------------------------------------------------------------------------------
-- Types and type classes used for characterizing optics
-------------------------------------------------------------------------------

record Copointed (f : Type -> Type) : Type where
  field extract : f a -> a

open Copointed {{...}} public

instance
  Copointed-Identity : Copointed Identity
  Copointed-Identity .extract = runIdentity

record Tagged (s b : Type) : Type where
  constructor Tagged:
  field unTagged : b

open Tagged public

instance
  Functor-Tagged : Functor (Tagged s)
  Functor-Tagged .map f (Tagged: x) = Tagged: (f x)

  Profunctor-Tagged : Profunctor Tagged
  Profunctor-Tagged .lcmap _ (Tagged: x) = Tagged: x

  Choice-Tagged : Choice Tagged
  Choice-Tagged .left (Tagged: x) = Tagged: (Left x)

data Exchange (a b s t : Type) : Type where
  Exchange: : (s -> a) -> (b -> t) -> Exchange a b s t

instance
  Functor-Exchange : Functor (Exchange a b s)
  Functor-Exchange .map f (Exchange: sa bt) = Exchange: sa (f <<< bt)

  Profunctor-Exchange : Profunctor (Exchange a b)
  Profunctor-Exchange .lcmap f (Exchange: sa bt) = Exchange: (sa <<< f) bt

data Market (a b s t : Type) : Type where
  Market: : (b -> t) -> (s -> Either t a) -> Market a b s t

instance
  Functor-Market : Functor (Market a b s)
  Functor-Market .map f (Market: bt seta) =
    Market: (f <<< bt) (either (Left <<< f) Right <<< seta)

  Profunctor-Market : Profunctor (Market a b)
  Profunctor-Market .lcmap f (Market: bt seta) = Market: bt (seta <<< f)

  Choice-Market : Choice (Market a b)
  Choice-Market .left (Market: bt seta) =
    Market: (Left <<< bt) \ where
      (Left s) -> either (Left <<< Left) Right (seta s)
      (Right c) -> Left (Right c)

-------------------------------------------------------------------------------
-- Optic types ala Van Laarhoven
-------------------------------------------------------------------------------

Simple : (Type -> Type -> Type -> Type -> Type) -> Type -> Type -> Type
Simple Optic s a = Optic s s a a

Traversal : (s t a b : Type) -> Type
Traversal s t a b = forall {f} -> {{Applicative f}}
  -> (a -> f b) -> s -> f t

Typeter : (s t a b : Type) -> Type
Typeter s t a b = forall {f} -> {{Applicative f}} -> {{Copointed f}}
  -> (a -> f b) -> s -> f t

Fold : (s t a b : Type) -> Type
Fold s t a b = forall {f} -> {{Applicative f}} -> {{Contravariant f}}
  -> (a -> f b) -> s -> f t

Getter : (s t a b : Type) -> Type
Getter s t a b = forall {f} -> {{Functor f}} -> {{Contravariant f}}
  -> (a -> f b) -> s -> f t

Lens : (s t a b : Type) -> Type
Lens s t a b = forall {f} -> {{Functor f}}
  -> (a -> f b) -> s -> f t

Iso : (s t a b : Type) -> Type
Iso s t a b = forall {p} {f} -> {{Profunctor p}} -> {{Functor f}}
  -> p a (f b) -> p s (f t)

Prism : (s t a b : Type) -> Type
Prism s t a b = forall {p} {f} -> {{Choice p}} -> {{Applicative f}}
  -> p a (f b) -> p s (f t)

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

lens : (s -> a) -> (s -> b -> t) -> Lens s t a b
lens v u f s = map (u s) (f (v s))

prism : (b -> t)  -> (s -> Either t a) -> Prism s t a b
prism bt seta = dimap seta (either pure (map bt)) <<< right

prism' : (b -> s)  -> (s -> Maybe a) -> Prism s s a b
prism' bs sma = prism bs (\ s -> maybe (Left s) Right (sma s))

iso : (s -> a) -> (b -> t) -> Iso s t a b
iso f g = dimap f (map g)

-------------------------------------------------------------------------------
-- Getting operations
-------------------------------------------------------------------------------

Getting : (r s a : Type) -> Type
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
foldlOf l f z = map (flip appEndo z <<< getDual) (foldMapOf l (Dual: <<< Endo: <<< flip f))

toListOf : Getting (Endo (List a)) s a -> s -> List a
toListOf l = foldrOf l _::_ []

lengthOf : Getting (Dual (Endo Nat)) s a -> s -> Nat
lengthOf l = foldlOf l (\ n _ -> Suc n) 0

preview : Getting (Maybe (First a)) s a -> s -> Maybe a
preview l = map getFirst <<< foldMapOf l (Just <<< First:)

firstOf : Getting (First a) s a -> s -> a
firstOf l = getFirst <<< foldMapOf l First:

lastOf : Getting (Last a) s a -> s -> a
lastOf l = getLast <<< foldMapOf l Last:

traverseOf! : {{Functor f}}
  -> Getting (f r) s a -> (a -> f r) -> s -> f Unit
traverseOf! l f = map (const unit) <<< foldMapOf l f

forOf! : {{Functor f}}
  -> Getting (f r) s a -> s -> (a -> f r) -> f Unit
forOf! = flip <<< traverseOf!

-------------------------------------------------------------------------------
-- ASetter
-------------------------------------------------------------------------------

ASetter : (s t a b : Type) -> Type
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

AReview : (t b : Type) -> Type
AReview t b = Tagged b (Identity b) -> Tagged t (Identity t)

review : AReview t b -> b -> t
review p = runIdentity <<< unTagged <<< p <<< Tagged: <<< Identity:

-------------------------------------------------------------------------------
-- AnIso
-------------------------------------------------------------------------------

AnIso : (s t a b : Type) -> Type
AnIso s t a b = Exchange a b a (Identity b) -> Exchange a b s (Identity t)

withIso : AnIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso ai k =
  case ai (Exchange: id Identity:) of \ where
    (Exchange: sa bt) -> k sa (runIdentity <<< bt)

under : AnIso s t a b -> (t -> s) -> b -> a
under ai = withIso ai \ sa bt ts -> sa <<< ts <<< bt

mapping : {{Functor f}} -> {{Functor g}}
  -> AnIso s t a b -> Iso (f s) (g t) (f a) (g b)
mapping k = withIso k $ \ sa bt -> iso (map sa) (map bt)

-------------------------------------------------------------------------------
-- APrism
-------------------------------------------------------------------------------

APrism : (s t a b : Type) -> Type
APrism s t a b = Market a b a (Identity b) -> Market a b s (Identity t)

withPrism : APrism s t a b -> ((b -> t) -> (s -> Either t a) -> r) -> r
withPrism ap f =
  case ap (Market: Identity: Right) of \ where
    (Market: bt seta) ->
      f (runIdentity <<< bt) (either (Left <<< runIdentity) Right <<< seta)

matching : APrism s t a b -> s -> Either t a
matching ap = withPrism ap \ _ seta -> seta

isn't : APrism s t a b -> s -> Bool
isn't ap s = either (const True) (const False) (matching ap s)

is : APrism s t a b -> s -> Bool
is ap = not <<< isn't ap

-------------------------------------------------------------------------------
-- Some general optics
-------------------------------------------------------------------------------

mapped : {{Functor f}} -> ASetter (f a) (f b) a b
mapped = sets map

traversed : {{Traversable f}} -> Traversal (f a) (f b) a b
traversed = traverse

record Folded (s a : Type) : Type where
  field folded : {{Monoid r}} -> Getting r s a

open Folded {{...}} public

instance
  Folded-List : Folded (List a) a
  Folded-List .folded f xs =
    Const: $ foldr (\ x y -> getConst (f x) <> y) neutral xs

record Each (s t a b : Type) : Type where
  field each : Traversal s t a b

open Each {{...}} public

instance
  Each-Pair : Each (Pair a a) (Pair b b) a b
  Each-Pair .each f (a , b) = (| _,_ (f a) (f b) |)

  Each-Maybe : Each (Maybe a) (Maybe b) a b
  Each-Maybe .each = traverse

  Each-Either : Each (Either a a) (Either b b) a b
  Each-Either .each f (Left a) = map Left (f a)
  Each-Either .each f (Right a) = map Right (f a)

  Each-List : Each (List a) (List b) a b
  Each-List .each f = flip foldr (| [] |) \ where
    x ys -> (| _::_ (f x) ys |)

record Cons (s t a b : Type) : Type where
  field #Cons : Prism s t (Pair a s) (Pair b t)

open Cons {{...}} public

instance
  Cons-List : Cons (List a) (List b) a b
  Cons-List .#Cons = prism (uncurry _::_) \ where
    (a :: as) -> Right (a , as)
    [] -> Left []

-------------------------------------------------------------------------------
-- Some specific optics
-------------------------------------------------------------------------------

#fst : Lens (Pair a c) (Pair b c) a b
#fst k (a , c) = map (_, c) (k a)

#snd : Lens (Pair a b) (Pair a c) b c
#snd k (x , y) = map (x ,_) (k y)

#Left : Traversal (Either a c) (Either b c) a b
#Left f (Left x) = map Left (f x)
#Left _ (Right y) = pure (Right y)

#Right : Traversal (Either a b) (Either a c) b c
#Right f (Right y) = map Right (f y)
#Right _ (Left x) = pure (Left x)

#Just : Traversal (Maybe a) (Maybe b) a b
#Just f (Just x) = map Just (f x)
#Just _ Nothing = pure Nothing

#Nothing : Simple Traversal (Maybe a) Unit
#Nothing f Nothing = map (const Nothing) (f unit)
#Nothing _ j = pure j

#head : {{Cons s s a a}} -> Simple Traversal s a
#head = #Cons <<< #fst

#tail : {{Cons s s a a}} -> Simple Traversal s s
#tail = #Cons <<< #snd
