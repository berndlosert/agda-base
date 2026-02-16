module Control.Lens where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Reader
open import Control.Monad.State as State
open import Data.Distributive
open import Data.Functor.Contravariant
open import Data.Functor.Representable
open import Data.List as List using ()
open import Data.Monoid.All
open import Data.Monoid.Any
open import Data.Monoid.Dual
open import Data.Monoid.Endo
open import Data.Monoid.EndoM
open import Data.Monoid.Product
open import Data.Monoid.Sum
open import Data.Profunctor
open import Data.Profunctor.Choice
open import Data.Semigroup.First
open import Data.Semigroup.Last
open import Data.Semigroup.Strict
open import Data.Traversable

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Monoid.All public
open Data.Monoid.Any public
open Data.Monoid.Dual public
open Data.Monoid.Endo public
open Data.Monoid.EndoM public
open Data.Monoid.Sum public
open Data.Semigroup.First public
open Data.Semigroup.Last public
open Data.Semigroup.Strict public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c r s t : Type
    f g m : Type -> Type
    p : Type -> Type -> Type

-------------------------------------------------------------------------------
-- Getter
-------------------------------------------------------------------------------

Getter : (s t a b : Type) -> Type
Getter s t a b = forall {f} -> {{Functor f}} -> {{Contravariant f}}
  -> (a -> f b) -> s -> f t

Getter' : (s a : Type) -> Type
Getter' s a = Getter s s a a

-- AGetter is a concrete representative of Getter. A getter is just a
-- function s -> a. The CPS version of s -> a is s -> (a -> r) -> r.
-- Rearranging gives you (a -> r) -> s -> r. By using Const, we get the
-- asLast form of AGetter. Note that the point of writing it in this funny
-- form is to match the type of Getter.
AGetter : (r s a : Type) -> Type
AGetter r s a = (a -> Const r a) -> s -> Const r s

to : (s -> a) -> AGetter r s a
to f k = asConst <<< getConst <<< k <<< f

view : AGetter a s a -> s -> a
view g = getConst <<< g asConst

foldMapOf : AGetter r s a -> (a -> r) -> s -> r
foldMapOf l step = getConst <<< l (asConst <<< step)

foldOf : AGetter a s a -> s -> a
foldOf l = getConst <<< l asConst

foldrOf : AGetter (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf {r} {s} {a} l step init xs =
    appEndo (foldMapOf l step' xs) init
  where
    step' : a -> Endo r
    step' x = asEndo \ y -> step x y

foldlOf : AGetter (Dual (Strict Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldlOf {r} {s} {a} l step init xs =
    appEndo (getStrict $ getDual $ foldMapOf l step' xs) init
  where
    step' : a -> Dual (Strict Endo r)
    step' x = asDual $ asStrict $ asEndo \ y -> step y x

foldlMOf : {{Monad m}} -> AGetter (Dual (EndoM m r)) s a
  -> (r -> a -> m r) -> r -> s -> m r
foldlMOf {m} {r} {s} {a} l step init xs = 
    appEndoM (getDual $ foldMapOf l step' xs) init
  where
    step' : a -> Dual (EndoM m r)
    step' x = asDual $ asEndoM \ y -> step y x  

toListOf : AGetter (Endo (List a)) s a -> s -> List a
toListOf l = foldrOf l _::_ []

concatOf : AGetter (List r) s (List r) -> s -> List r
concatOf l = getConst <<< l asConst

concatMapOf : AGetter (List r) s a -> (a -> List r) -> s -> List r
concatMapOf = foldMapOf

lengthOf : AGetter (Dual (Strict Endo Nat)) s a -> s -> Nat
lengthOf l = foldlOf l (\ n _ -> suc n) 0

findOf : AGetter (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf l p = foldrOf l (\ x y -> if p x then just x else y) nothing

anyOf : AGetter Any s a -> (a -> Bool) -> s -> Bool
anyOf l p = getAny <<< foldMapOf l (asAny <<< p)

has : AGetter Any s a -> s -> Bool
has l = anyOf l (const true)

allOf : AGetter All s a -> (a -> Bool) -> s -> Bool
allOf l p = getAll <<< foldMapOf l (asAll <<< p)

hasn't : AGetter All s a -> s -> Bool
hasn't l = allOf l (const false)

noneOf : AGetter Any s a -> (a -> Bool) -> s -> Bool
noneOf l p = not <<< anyOf l p

orOf : AGetter Any s Bool -> s -> Bool
orOf l = getAny <<< foldMapOf l asAny

andOf : AGetter All s Bool -> s -> Bool
andOf l = getAll <<< foldMapOf l asAll

nullOf : AGetter All s a -> s -> Bool
nullOf = hasn't

notNullOf : AGetter Any s a -> s -> Bool
notNullOf = has

preview : AGetter (Maybe (First a)) s a -> s -> Maybe a
preview l = map getFirst <<< foldMapOf l (just <<< asFirst)

firstOf : AGetter (First a) s a -> s -> a
firstOf l = getFirst <<< foldMapOf l asFirst

lastOf : AGetter (Last a) s a -> s -> a
lastOf l = getLast <<< foldMapOf l asLast

sumOf : {{Monoid (Sum a)}} -> AGetter (Dual (Strict Endo a)) s a -> s -> a
sumOf {a} l = foldlOf l plus zero
  where
    plus : a -> a -> a
    plus x y = getSum (asSum x <> asSum y)

    zero : a
    zero = getSum mempty

productOf : {{Monoid (Product a)}} -> AGetter (Dual (Strict Endo a)) s a -> s -> a
productOf {a} l = foldlOf l times one
  where
    times : a -> a -> a
    times x y = getProduct (asProduct x <> asProduct y)

    one : a
    one = getProduct mempty

elemOf : {{Eq a}} -> AGetter Any s a -> a -> s -> Bool
elemOf l = anyOf l <<< _==_

notElemOf : {{Eq a}} -> AGetter All s a -> a -> s -> Bool
notElemOf l = allOf l <<< _/=_

minimumOf : {{Ord a}} -> AGetter (Dual (Strict Endo (Maybe a))) s a -> s -> Maybe a
minimumOf {a} l = foldlOf l mini nothing
  where
    mini : Maybe a -> a -> Maybe a
    mini nothing y = just $! y
    mini (just x) y = just $! min x y

maximumOf : {{Ord a}} -> AGetter (Dual (Strict Endo (Maybe a))) s a -> s -> Maybe a
maximumOf {a} l = foldlOf l maxi nothing
  where
    maxi : Maybe a -> a -> Maybe a
    maxi nothing y = just $! y
    maxi (just x) y = just $! max x y

minimumByOf : AGetter (Dual (Strict Endo (Maybe a))) s a
  -> (a -> a -> Ordering) -> s -> Maybe a
minimumByOf l cmp = let instance _ = order cmp in minimumOf l

maximumByOf : AGetter (Dual (Strict Endo (Maybe a))) s a
  -> (a -> a -> Ordering) -> s -> Maybe a
maximumByOf l cmp = let instance _ = order cmp in maximumOf l

traverseOf' : {{Functor f}}
  -> AGetter (f r) s a -> (a -> f r) -> s -> f Unit
traverseOf' l f = map (const tt) <<< foldMapOf l f

forOf' : {{Functor f}}
  -> AGetter (f r) s a -> s -> (a -> f r) -> f Unit
forOf' = flip <<< traverseOf'

-------------------------------------------------------------------------------
-- Fold
-------------------------------------------------------------------------------

Fold : (s t a b : Type) -> Type
Fold s t a b = forall {f} -> {{Applicative f}} -> {{Contravariant f}}
  -> (a -> f b) -> s -> f t

Fold' : (s a : Type) -> Type
Fold' s a = Fold s s a a

record Folded (s a : Type) : Type where
  field folded : {{Monoid r}} -> AGetter r s a

open Folded {{...}} public

instance
  Folded-List : Folded (List a) a
  Folded-List .folded f [] = mempty
  Folded-List .folded f (x :: xs) = asConst (getConst (f x)) <> folded f xs

-------------------------------------------------------------------------------
-- Setter
-------------------------------------------------------------------------------

record Settable (f : Type -> Type) : Type where
  field
    overlap {{Applicative-super}} : Applicative f
    overlap {{Distributive-super}} : Distributive f
    overlap {{Traversable-super}} : Traversable f
    untainted : f a -> a

open Settable {{...}} public

instance
  Settable-Identity : Settable Identity
  Settable-Identity .untainted = runIdentity

Setter : (s t a b : Type) -> Type
Setter s t a b = forall {f} -> {{Settable f}} -> (a -> f b) -> s -> f t

Setter' : (s a : Type) -> Type
Setter' s a = Setter s s a a

-- ASetter is a concrete representation of Setter. A setter is a
-- generalized map function: (a -> b) -> s -> t. We use Identity
-- to get it in the Setter form.
ASetter : (s t a b : Type) -> Type
ASetter s t a b = (a -> Identity b) -> s -> Identity t

over : ASetter s t a b -> (a -> b) -> s -> t
over g k = runIdentity <<< g (asIdentity <<< k)

set : ASetter s t a b -> b -> s -> t
set f b = runIdentity <<< f (\ _ -> asIdentity b)

sets : ((a -> b) -> s -> t) -> ASetter s t a b
sets f k = asIdentity <<< f (runIdentity <<< k)

mapped : {{Functor f}} -> ASetter (f a) (f b) a b
mapped = sets map

-------------------------------------------------------------------------------
-- Lens
-------------------------------------------------------------------------------

Lens : (s t a b : Type) -> Type
Lens s t a b = forall {f} -> {{Functor f}} -> (a -> f b) -> s -> f t

Lens' : (s a : Type) -> Type
Lens' s a = Lens s s a a

-- A lens is made up of two functions: a getter (view) and a setter (update).
lens : (s -> a) -> (s -> b -> t) -> Lens s t a b
lens v u f s = map (u s) (f (v s))

-------------------------------------------------------------------------------
-- Traversal
-------------------------------------------------------------------------------

Traversal : (s t a b : Type) -> Type
Traversal s t a b = forall {f} -> {{Applicative f}} -> (a -> f b) -> s -> f t

Traversal' : (s a : Type) -> Type
Traversal' s a = Traversal s s a a

-- Bazaar is a partially applied Traversal. It is reminiscent of Yoneda.
-- We use this to define ATraversal.
record Bazaar (a b t : Type) : Type where
  constructor bazaar
  field runBazaar : {{Applicative f}} -> (a -> f b) -> f t

open Bazaar public

sell : a -> Bazaar a b b
sell x = bazaar \ f -> f x

bazaar' : {{Applicative f}} -> (a -> f b) -> Bazaar a b t -> f t
bazaar' f (bazaar g) = g f

instance
  Functor-Bazaar : Functor (Bazaar a b)
  Functor-Bazaar .map f (bazaar g) = bazaar \ h -> map f (g h)

  Applicative-Bazaar : Applicative (Bazaar a b)
  Applicative-Bazaar ._<*>_ (bazaar f) (bazaar x) =
    bazaar \ h -> f h <*> x h
  Applicative-Bazaar .pure x = bazaar \ _ -> pure x

  Profunctor-Bazaar : Profunctor (Bazaar a)
  Profunctor-Bazaar .lcmap f (bazaar g) = bazaar \ h -> g (map f <<< h)

-- ATraversal is a concrete reprensantive of Traversal.
ATraversal : (s t a b : Type) -> Type
ATraversal s t a b = (a -> Bazaar a b b) -> s -> Bazaar a b t

outs : Bazaar a a t -> List a -> t
outs = evalState <$> bazaar' (state <<< \ x xs -> swap (List.unconsWithDefault x xs))

ins : Bazaar a a t -> List a
ins = toListOf (\ f baz -> phantom (bazaar' f baz))

partsOf : Traversal s t a a -> Lens s t (List a) (List a)
partsOf l f s = let b = l sell s in outs b <$> f (ins b)

filtered : (a -> Bool) -> Traversal' a a
filtered pred f s = if pred s then f s else pure s

record Each (s t a b : Type) : Type where
  field each : Traversal s t a b

open Each {{...}} public

instance
  Each-Tuple : Each (Tuple a a) (Tuple b b) a b
  Each-Tuple .each f (a , b) = (| f a , f b |)

  Each-Maybe : Each (Maybe a) (Maybe b) a b
  Each-Maybe .each f nothing = pure nothing
  Each-Maybe .each f (just x) = map pure (f x)

  Each-Either : Each (Either a a) (Either b b) a b
  Each-Either .each f (left a) = map left (f a)
  Each-Either .each f (right a) = map right (f a)

  Each-List : Each (List a) (List b) a b
  Each-List .each f [] = pure []
  Each-List .each f (x :: xs) = (| f x :: each f xs |)

record Ixed (i s a : Type) : Type where
  field ix : i -> Traversal' s a

open Ixed {{...}} public

instance
  Ixed-Function : {{Eq a}} -> Ixed a (a -> b) b
  Ixed-Function .ix x p f = p (f x) <&> \ y x' -> if x == x' then y else f x'

  Ixed-List : Ixed Nat (List a) a
  Ixed-List {a} .ix k f xs0 = go xs0 k
    where
      go : List a -> Nat -> _
      go [] _ = pure []
      go (x :: xs) 0 = f x <&> (_:: xs)
      go (x :: xs) (suc n) = (x ::_) <$> (go xs $! n)

-------------------------------------------------------------------------------
-- Iso
-------------------------------------------------------------------------------

Iso : (s t a b : Type) -> Type
Iso s t a b = forall {p} {f} -> {{Profunctor p}} -> {{Functor f}}
  -> p a (f b) -> p s (f t)

Iso' : (s a : Type) -> Type
Iso' s a = Iso s s a a

iso : (s -> a) -> (b -> t) -> Iso s t a b
iso f g = dimap f (map g)

data Exchange (a b s t : Type) : Type where
  exchange : (s -> a) -> (b -> t) -> Exchange a b s t

instance
  Functor-Exchange : Functor (Exchange a b s)
  Functor-Exchange .map f (exchange sa bt) = exchange sa (f <<< bt)

  Profunctor-Exchange : Profunctor (Exchange a b)
  Profunctor-Exchange .lcmap f (exchange sa bt) = exchange (sa <<< f) bt

AnIso : (s t a b : Type) -> Type
AnIso s t a b = Exchange a b a (Identity b) -> Exchange a b s (Identity t)

withIso : AnIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso ai k =
  case (ai (exchange id asIdentity)) \ where
    (exchange sa bt) -> k sa (runIdentity <<< bt)

under : AnIso s t a b -> (t -> s) -> b -> a
under ai = withIso ai \ sa bt ts -> sa <<< ts <<< bt

mapping : {{Functor f}} -> {{Functor g}}
  -> AnIso s t a b -> Iso (f s) (g t) (f a) (g b)
mapping k = withIso k \ sa bt -> iso (map sa) (map bt)

record Wrapped (s a : Type) : Type where
  field wrapped : Iso' s a

open Wrapped {{...}} public

instance
  Wrapped-Identity : Wrapped (Identity a) a
  Wrapped-Identity .wrapped = iso runIdentity asIdentity

  Wrapped-Const : Wrapped (Const a b) a
  Wrapped-Const .wrapped = iso getConst asConst

  Wrapped-All : Wrapped All Bool
  Wrapped-All .wrapped = iso getAll asAll

  Wrapped-Any : Wrapped Any Bool
  Wrapped-Any .wrapped = iso getAny asAny

  Wrapped-Dual : Wrapped (Dual a) a
  Wrapped-Dual .wrapped = iso getDual asDual

  Wrapped-Endo : Wrapped (Endo a) (a -> a)
  Wrapped-Endo .wrapped = iso appEndo asEndo

  Wrapped-First : Wrapped (First a) a
  Wrapped-First .wrapped = iso getFirst asFirst

  Wrapped-Last : Wrapped (Last a) a
  Wrapped-Last .wrapped = iso getLast asLast

-------------------------------------------------------------------------------
-- Review
-------------------------------------------------------------------------------

record Tagged (s b : Type) : Type where
  constructor tagged
  field unTagged : b

open Tagged public

instance
  Functor-Tagged : Functor (Tagged s)
  Functor-Tagged .map f (tagged x) = tagged (f x)

  Profunctor-Tagged : Profunctor Tagged
  Profunctor-Tagged .lcmap _ (tagged x) = tagged x

  Choice-Tagged : Choice Tagged
  Choice-Tagged .mapLeft (tagged x) = tagged (left x)

AReview : (t b : Type) -> Type
AReview t b = Tagged b (Identity b) -> Tagged t (Identity t)

review : AReview t b -> b -> t
review p = runIdentity <<< unTagged <<< p <<< tagged <<< asIdentity

-------------------------------------------------------------------------------
-- Prism
-------------------------------------------------------------------------------

Prism : (s t a b : Type) -> Type
Prism s t a b = forall {p} {f} -> {{Choice p}} -> {{Applicative f}}
  -> p a (f b) -> p s (f t)

Prism' : (s a : Type) -> Type
Prism' s a = Prism s s a a

prism : (b -> t) -> (s -> Either t a) -> Prism s t a b
prism bt seta = dimap seta (either pure (map bt)) <<< mapRight

prism' : (b -> s) -> (s -> Maybe a) -> Prism s s a b
prism' bs sma = prism bs (\ s -> maybe (left s) right (sma s))

data Market (a b s t : Type) : Type where
  market : (b -> t) -> (s -> Either t a) -> Market a b s t

instance
  Functor-Market : Functor (Market a b s)
  Functor-Market .map f (market bt seta) =
    market (f <<< bt) (either (left <<< f) right <<< seta)

  Profunctor-Market : Profunctor (Market a b)
  Profunctor-Market .lcmap f (market bt seta) = market bt (seta <<< f)

  Choice-Market : Choice (Market a b)
  Choice-Market .mapLeft (market bt seta) =
    market (left <<< bt) \ where
      (left s) -> either (left <<< left) right (seta s)
      (right c) -> left (right c)

APrism : (s t a b : Type) -> Type
APrism s t a b = Market a b a (Identity b) -> Market a b s (Identity t)

withPrism : APrism s t a b -> ((b -> t) -> (s -> Either t a) -> r) -> r
withPrism ap f =
  case (ap (market asIdentity right)) \ where
    (market bt seta) ->
      f (runIdentity <<< bt) (either (left <<< runIdentity) right <<< seta)

matching : APrism s t a b -> s -> Either t a
matching ap = withPrism ap \ _ seta -> seta

isn't : APrism s t a b -> s -> Bool
isn't ap s = either (const true) (const false) (matching ap s)

is : APrism s t a b -> s -> Bool
is ap = not <<< isn't ap

-------------------------------------------------------------------------------
-- Operators
-------------------------------------------------------------------------------

infixl 8 _^:_
_^:_ : s -> AGetter a s a -> a
_^:_ = flip view

infixl 8 _^::_
_^::_ : s -> AGetter (Endo (List a)) s a -> List a
_^::_ = flip toListOf

infixl 8 _^?_
_^?_ : s -> AGetter (Maybe (First a)) s a -> Maybe a
_^?_ = flip preview

infixr 4 _:~_
_:~_ : ASetter s t a b -> b -> s -> t
_:~_ = set

infix 4 _:=_
_:=_ : {{MonadState s m}} -> ASetter s s a b -> b -> m Unit
l := b = State.modify (l :~ b)

infixr 4 _%~_
_%~_ : ASetter s t a b -> (a -> b) -> s -> t
_%~_ = over

infix 4 _%=_
_%=_ : {{MonadState s m}} -> ASetter s s a b -> (a -> b) -> m Unit
l %= f = State.modify (l %~ f)

infixr 4 _%%~_
_%%~_ : ((a -> f b) -> s -> f t) -> (a -> f b) -> s -> f t
_%%~_ = id

infix 4 _%%=_
_%%=_ : {{MonadState s m}} -> (p a (Tuple b r) -> s -> (Tuple s r)) -> p a (Tuple b r) -> m r
l %%= f = State.state (l f)

-------------------------------------------------------------------------------
-- Any specific optics
-------------------------------------------------------------------------------

#just : Prism (Maybe a) (Maybe b) a b
#just = prism just (maybe (left nothing) right)

#nothing : Prism' (Maybe a) Unit
#nothing = prism' (const nothing) (maybe (just tt) (const nothing))

#fst : Lens (Tuple a c) (Tuple b c) a b
#fst k (a , c) = map (_, c) (k a)

#snd : Lens (Tuple a b) (Tuple a c) b c
#snd k (x , y) = map (x ,_) (k y)

#left : Prism (Either a c) (Either b c) a b
#left = prism left (either right (left <<< right))

#right : Prism (Either a b) (Either a c) b c
#right = prism right (either (left <<< left) right)

#represented : {{r : Representable f}} -> Iso' (f a) (Reader (Rep f) a)
#represented = iso (asks <<< index) (tabulate <<< runReader)
