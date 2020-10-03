{-# OPTIONS --type-in-type #-}

module Control.Lens where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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

record Tagged (s b : Set) : Set where
  constructor Tagged:
  field unTagged : b

open Tagged public

instance
  Profunctor-Tagged : Profunctor Tagged
  Profunctor-Tagged .dimap _ f (Tagged: x) = Tagged: (f x)

  Choice-Tagged : Choice Tagged
  Choice-Tagged .lchoice (Tagged: x) = Tagged: (Left x)

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

Lens : (s t a b : Set) -> Set
Lens s t a b = forall {f} {{_ : Functor f}}
  -> (a -> f b) -> s -> f t

Getter : (s t a b : Set) -> Set
Getter s t a b = forall {f} {{_ : Functor f}} {{_ : Contravariant f}}
  -> (a -> f b) -> s -> f t

Prism : (s t a b : Set) -> Set
Prism s t a b = forall {p} {{_ : Choice p}} {f} {{_ : Functor f}}
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

countOf : Getting (Dual (Endo Int)) s a -> s -> Int
countOf l = foldlOf l (\ a _ -> a + 1) 0

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
-- ASetter operations
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
-- AReview operations
-------------------------------------------------------------------------------

AReview : (t b : Set) -> Set
AReview t b = Tagged b (Identity b) -> Tagged t (Identity t)

review : AReview t b -> b -> t
review p = runIdentity <<< unTagged <<< p <<< Tagged: <<< Identity:

-------------------------------------------------------------------------------
-- Lens operations
-------------------------------------------------------------------------------

lens : (s -> a) -> (s -> b -> t) -> Lens s t a b
lens v u f s = map (u s) (f (v s))

-------------------------------------------------------------------------------
-- Some general optics
-------------------------------------------------------------------------------

mapped : {{_ : Functor f}} -> ASetter (f a) (f b) a b
mapped = sets map

folded : {{_ : IsFoldable s a}} {{_ : Monoid r}} -> Getting r s a
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
