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
  constructor aTagged
  field unTagged : b

open Tagged public

instance
  Functor-Tagged : Functor (Tagged s)
  Functor-Tagged .map f (aTagged x) = aTagged (f x)

  Profunctor-Tagged : Profunctor Tagged
  Profunctor-Tagged .lcmap _ (aTagged x) = aTagged x

  Choice-Tagged : Choice Tagged
  Choice-Tagged .choicel (aTagged x) = aTagged (left x)

data Exchange (a b s t : Set) : Set where
  anExchange : (s -> a) -> (b -> t) -> Exchange a b s t

instance
  Functor-Exchange : Functor (Exchange a b s)
  Functor-Exchange .map f (anExchange sa bt) = anExchange sa (f <<< bt)

  Profunctor-Exchange : Profunctor (Exchange a b)
  Profunctor-Exchange .lcmap f (anExchange sa bt) = anExchange (sa <<< f) bt

data Market (a b s t : Set) : Set where
  aMarket : (b -> t) -> (s -> Either t a) -> Market a b s t

instance
  Functor-Market : Functor (Market a b s)
  Functor-Market .map f (aMarket bt seta) =
    aMarket (f <<< bt) (either (left <<< f) right <<< seta)

  Profunctor-Market : Profunctor (Market a b)
  Profunctor-Market .lcmap f (aMarket bt seta) = aMarket bt (seta <<< f)

  Choice-Market : Choice (Market a b)
  Choice-Market .choicel (aMarket bt seta) =
    aMarket (left <<< bt) \ where
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
-- AGetter operations
-------------------------------------------------------------------------------

AGetter : (r s a : Set) -> Set
AGetter r s a = (a -> Const r a) -> s -> Const r s

to : (s -> a) -> AGetter r s a
to f k = aConst <<< getConst <<< k <<< f

view : AGetter a s a -> s -> a
view g = getConst <<< g aConst

foldMapOf : AGetter r s a -> (a -> r) -> s -> r
foldMapOf l step = getConst <<< l (aConst <<< step)

foldOf : AGetter a s a -> s -> a
foldOf l = getConst <<< l aConst

foldrOf : AGetter (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf l step init = flip appEndo init <<< foldMapOf l (anEndo <<< step)

foldlOf : AGetter (Dual (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldlOf l step init =
  map
    (flip appEndo init <<< getDual)
    (foldMapOf l (aDual <<< anEndo <<< flip step))

foldlMOf : {{Monad m}} -> AGetter (Endo (r -> m r)) s a
  -> (r -> a -> m r) -> r -> s -> m r
foldlMOf l step init xs = foldrOf l (\ x k acc -> step acc x >>= k) pure xs init

toListOf : AGetter (Endo (List a)) s a -> s -> List a
toListOf l = foldrOf l _::_ []

has : AGetter Any s a -> s -> Bool
has l = getAny <<< foldMapOf l (\ _ -> anAny true)

hasn't : AGetter All s a -> s -> Bool
hasn't l = getAll <<< foldMapOf l (\ _ -> anAll false)

lengthOf : AGetter (Dual (Endo Nat)) s a -> s -> Nat
lengthOf l = foldlOf l (\ n _ -> suc n) zero

preview : AGetter (Maybe (First a)) s a -> s -> Maybe a
preview l = map getFirst <<< foldMapOf l (just <<< aFirst)

firstOf : AGetter (First a) s a -> s -> a
firstOf l = getFirst <<< foldMapOf l aFirst

lastOf : AGetter (Last a) s a -> s -> a
lastOf l = getLast <<< foldMapOf l aLast

findOf : AGetter (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf l p = foldrOf l (\ x y -> if p x then just x else y) nothing

traverseOf! : {{Functor f}}
  -> AGetter (f r) s a -> (a -> f r) -> s -> f Unit
traverseOf! l f = map (const tt) <<< foldMapOf l f

forOf! : {{Functor f}}
  -> AGetter (f r) s a -> s -> (a -> f r) -> f Unit
forOf! = flip <<< traverseOf!

-------------------------------------------------------------------------------
-- ASetter
-------------------------------------------------------------------------------

ASetter : (s t a b : Set) -> Set
ASetter s t a b = (a -> Identity b) -> s -> Identity t

over : ASetter s t a b -> (a -> b) -> s -> t
over g k = runIdentity <<< g (anIdentity <<< k)

set : ASetter s t a b -> b -> s -> t
set f b = runIdentity <<< f (\ _ -> anIdentity b)

sets : ((a -> b) -> s -> t) -> ASetter s t a b
sets f k = anIdentity <<< f (runIdentity <<< k)

-------------------------------------------------------------------------------
-- AReview
-------------------------------------------------------------------------------

AReview : (t b : Set) -> Set
AReview t b = Tagged b (Identity b) -> Tagged t (Identity t)

review : AReview t b -> b -> t
review p = runIdentity <<< unTagged <<< p <<< aTagged <<< anIdentity

-------------------------------------------------------------------------------
-- AnIso
-------------------------------------------------------------------------------

AnIso : (s t a b : Set) -> Set
AnIso s t a b = Exchange a b a (Identity b) -> Exchange a b s (Identity t)

withIso : AnIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso ai k =
  case ai (anExchange id anIdentity) of \ where
    (anExchange sa bt) -> k sa (runIdentity <<< bt)

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
  case ap (aMarket anIdentity right) of \ where
    (aMarket bt seta) ->
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
  field folded : {{Monoid r}} -> AGetter r s a

open Folded {{...}} public

instance
  Folded-List : Folded (List a) a
  Folded-List .folded f [] = mempty
  Folded-List .folded f (x :: xs) = aConst (getConst $ f x) <> folded f xs

record Each (s t a b : Set) : Set where
  field each : Traversal s t a b

open Each {{...}} public

instance
  Each-Pair : Each (Pair a a) (Pair b b) a b
  Each-Pair .each f (a , b) = (| f a , f b |)

  Each-Maybe : Each (Maybe a) (Maybe b) a b
  Each-Maybe .each f nothing = pure nothing
  Each-Maybe .each f (just x) = map pure (f x)

  Each-Either : Each (Either a a) (Either b b) a b
  Each-Either .each f (left a) = map left (f a)
  Each-Either .each f (right a) = map right (f a)

  Each-List : Each (List a) (List b) a b
  Each-List .each f [] = pure []
  Each-List .each f (x :: xs) = (| f x :: each f xs |)

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
