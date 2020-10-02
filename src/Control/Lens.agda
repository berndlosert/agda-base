{-# OPTIONS --type-in-type #-}

module Control.Lens where

open import Prelude

private
  variable
    a b c r s t : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Additional yype classes used for characterizing optics
-------------------------------------------------------------------------------

record Copointed (f : Set -> Set) : Set where
  field extract : f a -> a

open Copointed {{...}}

instance
  Copointed-Identity : Copointed Identity
  Copointed-Identity .extract = runIdentity

-------------------------------------------------------------------------------
-- Optics ala Van Laarhoven
-------------------------------------------------------------------------------

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

Simple : (Set -> Set -> Set -> Set -> Set) -> Set -> Set -> Set
Simple Optic s a = Optic s s a a

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

foldrOf : Getting (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf l f z = flip appEndo z <<< foldMapOf l (Endo: <<< f)

foldlOf : Getting (Dual (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldlOf l f z = rmap (flip appEndo z <<< getDual) (foldMapOf l (Dual: <<< Endo: <<< flip f))

toListOf : Getting (Endo (List a)) s a -> s -> List a
toListOf l = foldrOf l _::_ []

lengthOf : Getting (Dual (Endo Int)) s a -> s -> Int
lengthOf l = foldlOf l (\ a _ -> a + 1) 0

preview : Getting (Maybe (First a)) s a -> s -> Maybe a
preview l = map getFirst <<< foldMapOf l (Just <<< First:)

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
-- Lens operations
-------------------------------------------------------------------------------

lens : (s -> a) -> (s -> b -> t) -> Lens s t a b
lens v u f s = map (u s) (f (v s))

-------------------------------------------------------------------------------
-- Each and instances
-------------------------------------------------------------------------------

record Each (s t a b : Set) : Set where
  field each : Traversal s t a b

open Each {{...}} public

instance
  Each-List : Each (List a) (List b) a b
  Each-List .each = traverse

-------------------------------------------------------------------------------
-- Basic lenses and traversals
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
