{-# OPTIONS --type-in-type #-}

module Prelude where

-------------------------------------------------------------------------------
-- Primitive types
-------------------------------------------------------------------------------

data Void : Set where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit)
  using (tt)

open import Agda.Builtin.Bool public
  using (Bool)
  using (false)
  using (true)

data Ordering : Set where
  LT EQ GT : Ordering

{-# COMPILE GHC Ordering = data Ordering (LT | EQ | GT) #-}

open import Agda.Builtin.Nat public
  using (Nat)
  using (zero)
  using (suc)

open import Agda.Builtin.Int public
  using (Int)
  using (pos)
  using (negsuc)

open import Agda.Builtin.Float public
  using (Float)

open import Agda.Builtin.Char public
  using (Char)

open import Agda.Builtin.String public
  using (String)

open import Agda.Builtin.Equality public
  renaming (_≡_ to _===_)
  using (refl)

Function : Set -> Set -> Set
Function a b = a -> b

data Either (a b : Set) : Set where
  left : a -> Either a b
  right : b -> Either a b

{-# COMPILE GHC Either = data Either (Left | Right) #-}

open import Agda.Builtin.Sigma public
  renaming (Σ to DPair)
  hiding (_,_)

infixl 1 _,_
record Pair (a b : Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b

open Pair public

{-# COMPILE GHC Pair = data (,) ((,)) #-}

open import Agda.Builtin.Maybe public
  using (Maybe)
  using (nothing)
  using (just)

open import Agda.Builtin.List public
  using (List)
  using ([])
  renaming (_∷_ to _::_)

open import Agda.Builtin.IO public
  using (IO)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c d l r s v : Set
    f m : Set -> Set
    p : Set -> Set -> Set

-------------------------------------------------------------------------------
-- Dangerous primitives
-------------------------------------------------------------------------------

record Partial : Set where
  field oops : Void

open Partial {{...}} public

postulate
  trustMe : a
  error : String -> a

undefined : {{Partial}} -> a
undefined = error "Prelude.undefined"

unsafePerform : ({{Partial}} -> a) -> a
unsafePerform x = x {{trustMe}}

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC error = \ _ s -> error (Data.Text.unpack s) #-}

-------------------------------------------------------------------------------
-- Function primitives
-------------------------------------------------------------------------------

the : (a : Set) -> a -> a
the _ x = x

const : a -> b -> a
const x _ = x

flip : (a -> b -> c) -> b -> a -> c
flip f x y = f y x

infixr 0 _$_
_$_ : (a -> b) -> a -> b
f $ x = f x

infixl 1 _#_
_#_ : a -> (a -> b) -> b
_#_ x f = f x

case_of_ : a -> (a -> b) -> b
case_of_ x f = f x

-------------------------------------------------------------------------------
-- Strictness primitives
-------------------------------------------------------------------------------

open import Agda.Builtin.Strict

infixr 0 _$!_
_$!_ : (a -> b) -> a -> b
f $! x = primForce x f

seq : a -> b -> b
seq a b = const b $! a

-------------------------------------------------------------------------------
-- Bool primitives
-------------------------------------------------------------------------------

Assert : Bool -> Set
Assert false = Void
Assert true = Unit

bool : a -> a -> Bool -> a
bool x _ false = x
bool _ x true = x

infixr 0 if_then_else_
if_then_else_ : Bool -> a -> a -> a
if b then x else y = bool y x b

not : Bool -> Bool
not false = true
not true = false

infixr 2 _||_
_||_ : Bool -> Bool -> Bool
false || x = x
true || _ = true

infixr 3 _&&_
_&&_ : Bool -> Bool -> Bool
false && _ = false
true && x = x

infixr 0 _implies_
_implies_ : Bool -> Bool -> Bool
x implies y = not x || y

-------------------------------------------------------------------------------
-- Nat primitives
-------------------------------------------------------------------------------

applyN : Nat -> (a -> a) -> a -> a
applyN 0 _ x = x
applyN (suc n) f x = f (applyN n f x)

monus : Nat -> Nat -> Nat
monus = Agda.Builtin.Nat._-_

pred : Nat -> Nat
pred 0 = 0
pred (suc n) = n

-------------------------------------------------------------------------------
-- Int primitives
-------------------------------------------------------------------------------

neg : Nat -> Int
neg 0 = pos 0
neg (suc n) = negsuc n

diff : Nat -> Nat -> Int
diff m 0 = pos m
diff zero (suc n) = negsuc n
diff (suc m) (suc n) = diff m n

------------------------------------------------------------------------------
-- Either primitives
-------------------------------------------------------------------------------

either : (a -> c) -> (b -> c) -> Either a b -> c
either f g (left x) = f x
either f g (right x) = g x

mirror : Either a b -> Either b a
mirror = either right left

fromEither : Either a a -> a
fromEither (left x) = x
fromEither (right x) = x

isLeft : Either a b -> Bool
isLeft (left _) = true
isLeft _ = false

isRight : Either a b -> Bool
isRight (left _) = false
isRight _ = true

fromLeft : (val : Either a b) -> {{Assert $ isLeft val}} -> a
fromLeft (left x) = x
fromLeft _ = error "Prelude.fromLeft: bad argument"

fromRight : (val : Either a b) -> {{Assert $ isRight val}} -> b
fromRight (right x) = x
fromRight  _ = error "Prelude.fromRight: bad argument"

-------------------------------------------------------------------------------
-- Pair primitives
-------------------------------------------------------------------------------

pair : (a -> b) -> (a -> c) -> a -> Pair b c
pair f g x = (f x , g x)

swap : Pair a b -> Pair b a
swap = pair snd fst

dup : a -> Pair a a
dup x = (x , x)

uncurry : (a -> b -> c) -> Pair a b -> c
uncurry f (x , y) = f x y

curry : (Pair a b -> c) -> a -> b -> c
curry f x y = f (x , y)

apply : Pair (a -> b) a -> b
apply (f , x) = f x

-------------------------------------------------------------------------------
-- Maybe primitives
-------------------------------------------------------------------------------

isJust : Maybe a -> Bool
isJust (just _) = true
isJust _ = false

isNothing : Maybe a -> Bool
isNothing (just _) = false
isNothing _ = true

fromJust : (val : Maybe a) -> {{Assert $ isJust val}} -> a
fromJust (just a) = a
fromJust nothing = error "Prelude.fromJust: bad argument"

maybe : b -> (a -> b) -> Maybe a -> b
maybe b f nothing = b
maybe b f (just a) = f a

fromMaybe : a -> Maybe a -> a
fromMaybe _ (just x) = x
fromMaybe x nothing = x

-------------------------------------------------------------------------------
-- IO primitives
-------------------------------------------------------------------------------

private
  postulate
    mapIO : (a -> b) -> IO a -> IO b
    pureIO : a -> IO a
    apIO : IO (a -> b) -> IO a -> IO b
    bindIO : IO a -> (a -> IO b) -> IO b

{-# COMPILE GHC mapIO = \ _ _ -> fmap #-}
{-# COMPILE GHC pureIO = \ _ -> pure #-}
{-# COMPILE GHC apIO = \ _ _ -> (<*>) #-}
{-# COMPILE GHC bindIO = \ _ _ -> (>>=) #-}

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

record Eq (a : Set) : Set where
  infix 4 _==_
  field _==_ : a -> a -> Bool

  infix 4 _/=_
  _/=_ : a -> a -> Bool
  x /= y = if x == y then false else true

  equating : (b -> a) -> b -> b -> Bool
  equating f x y = f x == f y

open Eq {{...}} public

instance
  Eq-Void : Eq Void
  Eq-Void ._==_ = \ ()

  Eq-Unit : Eq Unit
  Eq-Unit ._==_ tt tt = true

  Eq-Bool : Eq Bool
  Eq-Bool ._==_ = \ where
    true true -> true
    false false -> false
    _ _ -> false

  Eq-Ordering : Eq Ordering
  Eq-Ordering ._==_ = \ where
    LT LT -> true
    EQ EQ -> true
    GT GT -> true
    _ _ -> false

  Eq-Nat : Eq Nat
  Eq-Nat ._==_ = Agda.Builtin.Nat._==_

  Eq-Int : Eq Int
  Eq-Int ._==_ = \ where
    (pos m) (pos n) -> m == n
    (negsuc m) (negsuc n) -> m == n
    _ _ -> false

  Eq-Float : Eq Float
  Eq-Float ._==_ = Agda.Builtin.Float.primFloatEquality

  Eq-Char : Eq Char
  Eq-Char ._==_ = Agda.Builtin.Char.primCharEquality

  Eq-String : Eq String
  Eq-String ._==_ = Agda.Builtin.String.primStringEquality

  Eq-Either : {{Eq a}} -> {{Eq b}} -> Eq (Either a b)
  Eq-Either ._==_ = \ where
    (left x) (left y) -> x == y
    (right x) (right y) -> x == y
    _ _ -> false

  Eq-Pair : {{Eq a}} -> {{Eq b}} -> Eq (Pair a b)
  Eq-Pair ._==_ (x , y) (w , z) = (x == w) && (y == z)

  Eq-Maybe : {{Eq a}} -> Eq (Maybe a)
  Eq-Maybe ._==_ = \ where
    nothing nothing -> true
    (just x) (just y) -> x == y
    _ _ -> false

  Eq-List : {{Eq a}} -> Eq (List a)
  Eq-List ._==_ = \ where
    [] [] -> true
    (x :: xs) (y :: ys) -> x == y && xs == ys
    _ _ -> false

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

record Ord (a : Set) : Set where
  field
    overlap {{Eq-super}} : Eq a
    compare : a -> a -> Ordering

  comparing : (b -> a) -> b -> b -> Ordering
  comparing f x y = compare (f x) (f y)

  infixl 4 _<_
  _<_ : a -> a -> Bool
  x < y = case compare x y of \ where
    LT -> true
    _ -> false

  infixl 4 _>_
  _>_ : a -> a -> Bool
  _>_ = flip _<_

  infixl 4 _<=_
  _<=_ : a -> a -> Bool
  x <= y = case compare x y of \ where
    GT -> false
    _ -> true

  infixl 4 _>=_
  _>=_ : a -> a -> Bool
  _>=_ = flip _<=_

  min : a -> a -> a
  min x y = if x < y then x else y

  max : a -> a -> a
  max x y = if x < y then y else x

open Ord {{...}} public

instance
  Ord-Void : Ord Void
  Ord-Void .compare = \ ()

  Ord-Unit : Ord Unit
  Ord-Unit .compare tt tt = EQ

  Ord-Bool : Ord Bool
  Ord-Bool .compare false true = LT
  Ord-Bool .compare true false = GT
  Ord-Bool .compare _ _ = EQ

  Ord-Ordering : Ord Ordering
  Ord-Ordering .compare LT EQ = LT
  Ord-Ordering .compare LT GT = LT
  Ord-Ordering .compare EQ LT = GT
  Ord-Ordering .compare EQ GT = LT
  Ord-Ordering .compare GT LT = GT
  Ord-Ordering .compare GT EQ = GT
  Ord-Ordering .compare _ _ = EQ

  Ord-Nat : Ord Nat
  Ord-Nat .compare m n =
    if m == n then EQ
    else if Agda.Builtin.Nat._<_ m n then LT
    else GT

  Ord-Int : Ord Int
  Ord-Int .compare = \ where
    (pos m) (pos n) -> compare m n
    (negsuc m) (negsuc n) -> compare n m
    (pos _) (negsuc _) -> GT
    (negsuc _) (pos _) -> LT

  Ord-Float : Ord Float
  Ord-Float .compare x y =
    if x == y then EQ
    else if Agda.Builtin.Float.primFloatLess x y then LT
    else GT

  Ord-Char : Ord Char
  Ord-Char .compare l r =
    let ord = Agda.Builtin.Char.primCharToNat
    in compare (ord l) (ord r)

  Ord-List : {{Ord a}} -> Ord (List a)
  Ord-List .compare [] [] = EQ
  Ord-List .compare [] (x :: xs) = LT
  Ord-List .compare (x :: xs) [] = GT
  Ord-List .compare (x :: xs) (y :: ys) =
    case compare x y of \ where
      LT -> LT
      EQ -> compare xs ys
      GT -> GT

  Ord-String : Ord String
  Ord-String .compare l r =
    let unpack = Agda.Builtin.String.primStringToList
    in compare (unpack l) (unpack r)

  Ord-Pair : {{Ord a}} -> {{Ord b}} -> Ord (Pair a b)
  Ord-Pair .compare (x , y) (w , z) =
    case compare x w of \ where
      LT -> LT
      GT -> GT
      EQ -> compare y z

  Ord-Maybe : {{Ord a}} -> Ord (Maybe a)
  Ord-Maybe .compare nothing nothing = EQ
  Ord-Maybe .compare nothing _ = LT
  Ord-Maybe .compare (just x) (just y) = compare x y
  Ord-Maybe .compare (just _) _ = GT

-------------------------------------------------------------------------------
-- FromNat
-------------------------------------------------------------------------------

record FromNat (a : Set) : Set where
  field
    FromNatConstraint : Nat -> Set
    fromNat : (n : Nat) -> {{FromNatConstraint n}} -> a

open FromNat {{...}} public

{-# BUILTIN FROMNAT fromNat #-}

instance
  FromNat-Nat : FromNat Nat
  FromNat-Nat .FromNatConstraint _ = Unit
  FromNat-Nat .fromNat n = n

  FromNat-Int : FromNat Int
  FromNat-Int .FromNatConstraint _ = Unit
  FromNat-Int .fromNat n = pos n

  FromNat-Float : FromNat Float
  FromNat-Float .FromNatConstraint _ = Unit
  FromNat-Float .fromNat n = Agda.Builtin.Float.primNatToFloat n

-------------------------------------------------------------------------------
-- ToNat
-------------------------------------------------------------------------------

record ToNat (a : Set) : Set where
  field
    ToNatConstraint : a -> Set
    toNat : (x : a) -> {{ToNatConstraint x}} -> Nat

open ToNat {{...}} public

instance
  ToNat-Int : ToNat Int
  ToNat-Int .ToNatConstraint _ = Unit
  ToNat-Int .toNat (pos n) = n
  ToNat-Int .toNat (negsuc n) = 0

-------------------------------------------------------------------------------
-- FromNeg
-------------------------------------------------------------------------------

record FromNeg (a : Set) : Set where
  field
    FromNegConstraint : Nat -> Set
    fromNeg : (n : Nat) -> {{FromNegConstraint n}} -> a

open FromNeg {{...}} public

{-# BUILTIN FROMNEG fromNeg #-}

instance
  FromNeg-Int : FromNeg Int
  FromNeg-Int .FromNegConstraint _ = Unit
  FromNeg-Int .fromNeg n = neg n

  FromNeg-Float : FromNeg Float
  FromNeg-Float .FromNegConstraint _ = Unit
  FromNeg-Float .fromNeg n =
    Agda.Builtin.Float.primFloatNegate (Agda.Builtin.Float.primNatToFloat n)

-------------------------------------------------------------------------------
-- Arithmetic operations
-------------------------------------------------------------------------------

record Add (a : Set) : Set where
  infixl 6 _+_
  field _+_ : a -> a -> a

open Add {{...}} public

record Sub (a : Set) : Set where
  infixl 6 _-_
  field
    Diff : Set
    _-_ : a -> a -> Diff

open Sub {{...}} public

record Neg (a : Set) : Set where
  field -_ : a -> a

open Neg {{...}} public

record Mul (a : Set) : Set where
  infixl 7 _*_
  field _*_ : a -> a -> a

open Mul {{...}} public

record Exp (a : Set) : Set where
  infixr 8 _^_
  field
    Power : Set
    _^_ : a -> Power -> a

open Exp {{...}} public

record Divisor (a : Set) : Set where
  field divisor : a -> Bool

open Divisor {{...}} public

record Div (a : Set) : Set where
  infixl 7 _/_
  field
    overlap {{Divisor-super}} : Divisor a
    _/_ : (x y : a) -> {{Assert $ divisor y}} -> a

open Div {{...}} public

record Mod (a : Set) : Set where
  infixl 7 _%_
  field
    overlap {{Divisor-super}} : Divisor a
    _%_ : (x y : a) -> {{Assert $ divisor y}} -> a

open Mod {{...}} public

instance
  Add-Nat : Add Nat
  Add-Nat ._+_ = Agda.Builtin.Nat._+_

  Sub-Nat : Sub Nat
  Sub-Nat .Diff = Nat
  Sub-Nat ._-_ = Agda.Builtin.Nat._-_

  Mul-Nat : Mul Nat
  Mul-Nat ._*_ = Agda.Builtin.Nat._*_

  Exp-Nat : Exp Nat
  Exp-Nat .Power = Nat
  Exp-Nat ._^_ m 0 = 1
  Exp-Nat ._^_ m (suc n) = m * m ^ n

  Divisor-Nat : Divisor Nat
  Divisor-Nat .divisor 0 = false
  Divisor-Nat .divisor _ = true

  Div-Nat : Div Nat
  Div-Nat .Divisor-super = Divisor-Nat
  Div-Nat ._/_ m (suc n) = Agda.Builtin.Nat.div-helper 0 n m n

  Mod-Nat : Mod Nat
  Mod-Nat .Divisor-super = Divisor-Nat
  Mod-Nat ._%_ m (suc n) = Agda.Builtin.Nat.mod-helper 0 n m n

  Add-Int : Add Int
  Add-Int ._+_ = \ where
    (negsuc m) (negsuc n) -> negsuc (suc (m + n))
    (negsuc m) (pos n) -> diff n (suc m)
    (pos m) (negsuc n) -> diff m (suc n)
    (pos m) (pos n) -> pos (m + n)

  Sub-Int : Sub Int
  Sub-Int .Diff = Int
  Sub-Int ._-_ = \ where
    m (pos n) -> m + (neg n)
    m (negsuc n) -> m + pos (suc n)

  Neg-Int : Neg Int
  Neg-Int .-_ = \ where
    (pos 0) -> pos 0
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)

  Mul-Int : Mul Int
  Mul-Int ._*_ = \ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> neg (n * suc m)
    (negsuc n) (pos m) -> neg (suc n * m)

  Exp-Int : Exp Int
  Exp-Int .Power = Nat
  Exp-Int ._^_ m 0 = pos 0
  Exp-Int ._^_ m (suc n) = m * m ^ n

  Divisor-Int : Divisor Int
  Divisor-Int .divisor (pos 0) = false
  Divisor-Int .divisor _ = true

  Div-Int : Div Int
  Div-Int .Divisor-super = Divisor-Int
  Div-Int ._/_ = \ where
    (pos m) (pos n@(suc _)) -> pos (m / n)
    (pos m) (negsuc n) -> neg (m / suc n)
    (negsuc m) (pos n@(suc _)) -> neg (suc m / n)
    (negsuc m) (negsuc n) -> pos (suc m / suc n)

  Mod-Int : Mod Int
  Mod-Int .Divisor-super = Divisor-Int
  Mod-Int ._%_ = \ where
    (pos m) (pos n@(suc _)) -> pos (m % n)
    (pos m) (negsuc n) -> pos (m % suc n)
    (negsuc m) (pos n@(suc _)) -> neg (suc m % n)
    (negsuc m) (negsuc n) -> neg (suc m % suc n)

  Add-Float : Add Float
  Add-Float ._+_ = Agda.Builtin.Float.primFloatPlus

  Sub-Float : Sub Float
  Sub-Float .Diff = Float
  Sub-Float ._-_ = Agda.Builtin.Float.primFloatMinus

  Neg-Float : Neg Float
  Neg-Float .-_ = Agda.Builtin.Float.primFloatNegate

  Mul-Float : Mul Float
  Mul-Float ._*_ = Agda.Builtin.Float.primFloatTimes

  Exp-Float : Exp Float
  Exp-Float .Power = Float
  Exp-Float ._^_ = Agda.Builtin.Float.primFloatPow

  Divisor-Float : Divisor Float
  Divisor-Float .divisor _ = true

  Div-Float : Div Float
  Div-Float ._/_ x y = Agda.Builtin.Float.primFloatDiv x y

-------------------------------------------------------------------------------
-- Semigroup
-------------------------------------------------------------------------------

record Semigroup (a : Set) : Set where
  infixr 5 _<>_
  field _<>_ : a -> a -> a

open Semigroup {{...}} public

instance
  Semigroup-Void : Semigroup Void
  Semigroup-Void ._<>_ = \ ()

  Semigroup-Unit : Semigroup Unit
  Semigroup-Unit ._<>_ tt tt = tt

  Semigroup-Ordering : Semigroup Ordering
  Semigroup-Ordering ._<>_ = \ where
    LT _ -> LT
    EQ y -> y
    GT _ -> GT

  Semigroup-String : Semigroup String
  Semigroup-String ._<>_ = Agda.Builtin.String.primStringAppend

  Semigroup-Function : {{Semigroup b}} -> Semigroup (a -> b)
  Semigroup-Function ._<>_ f g = \ x -> f x <> g x

  Semigroup-Either : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Either a b)
  Semigroup-Either ._<>_ (left _) x = x
  Semigroup-Either ._<>_ x _ = x

  Semigroup-Pair : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Pair a b)
  Semigroup-Pair ._<>_ (x , y) (w , z) = (x <> w , y <> z)

  Semigroup-Maybe : {{Semigroup a}} -> Semigroup (Maybe a)
  Semigroup-Maybe ._<>_ = \ where
    nothing x -> x
    x nothing -> x
    (just x) (just y) -> just (x <> y)

  Semigroup-List : Semigroup (List a)
  Semigroup-List ._<>_ = \ where
    [] ys -> ys
    (x :: xs) ys -> x :: (xs <> ys)

  Semigroup-IO : {{Semigroup a}} -> Semigroup (IO a)
  Semigroup-IO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| x <> y |)

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Set) : Set where
  field
    overlap {{Semigroup-super}} : Semigroup a
    mempty : a

  mtimes : Nat -> a -> a
  mtimes 0 _ = mempty
  mtimes (suc n) x = x <> mtimes n x

open Monoid {{...}} public

instance
  Monoid-Unit : Monoid Unit
  Monoid-Unit .mempty = tt

  Monoid-Ordering : Monoid Ordering
  Monoid-Ordering .mempty = EQ

  Monoid-String : Monoid String
  Monoid-String .mempty = ""

  Monoid-Function : {{Monoid b}} -> Monoid (a -> b)
  Monoid-Function .mempty = const mempty

  Monoid-Pair : {{Monoid a}} -> {{Monoid b}} -> Monoid (Pair a b)
  Monoid-Pair .mempty = (mempty , mempty)

  Monoid-Maybe : {{Semigroup a}} -> Monoid (Maybe a)
  Monoid-Maybe .mempty = nothing

  Monoid-List : Monoid (List a)
  Monoid-List .mempty = []

  Monoid-IO : {{Monoid a}} -> Monoid (IO a)
  Monoid-IO .mempty = pureIO mempty

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

record Category (p : Set -> Set -> Set) : Set where
  infixr 9 _<<<_
  field
    _<<<_ : p b c -> p a b -> p a c
    id : p a a

  infixr 9 _>>>_
  _>>>_ : p a b -> p b c -> p a c
  _>>>_ = flip _<<<_

open Category {{...}} public

instance
  Category-Function : Category Function
  Category-Function ._<<<_ f g x = f (g x)
  Category-Function .id x = x

-------------------------------------------------------------------------------
-- Functor
-------------------------------------------------------------------------------

record Functor (f : Set -> Set) : Set where
  field map : (a -> b) -> f a -> f b

  infixl 4 _<$>_
  _<$>_ : (a -> b) -> f a -> f b
  _<$>_ = map

  infixl 1 _<#>_
  _<#>_ : f a -> (a -> b) -> f b
  _<#>_ = flip map

  infixl 4 _<$_
  _<$_ : b -> f a -> f b
  _<$_ = map <<< const

  infixl 4 _$>_
  _$>_ : f a -> b -> f b
  _$>_ = flip _<$_

  ignore : f a -> f Unit
  ignore = tt <$_

  vacuous : f Void -> f a
  vacuous = map \ ()

open Functor {{...}} public

instance
  Functor-Function : Functor (Function a)
  Functor-Function .map = _<<<_

  Functor-Either : Functor (Either a)
  Functor-Either .map f = either left (right <<< f)

  Functor-Pair : Functor (Pair a)
  Functor-Pair .map f (x , y) = (x , f y)

  Functor-Maybe : Functor Maybe
  Functor-Maybe .map f = maybe nothing (just <<< f)

  Functor-List : Functor List
  Functor-List .map f = \ where
    [] -> []
    (x :: xs) -> f x :: map f xs

  Functor-IO : Functor IO
  Functor-IO .map = mapIO

-------------------------------------------------------------------------------
-- Contravariant
-------------------------------------------------------------------------------

record Contravariant (f : Set -> Set) : Set where
  field cmap : (a -> b) -> f b -> f a

  phantom : {{Functor f}} -> f a -> f b
  phantom x = cmap (const tt) (map (const tt) x)

open Contravariant {{...}} public

-------------------------------------------------------------------------------
-- Bifunctor
-------------------------------------------------------------------------------

record Bifunctor (p : Set -> Set -> Set) : Set where
  field
    overlap {{Functor-super}} : Functor (p a)
    lmap : (a -> b) -> p a c -> p b c

  bimap : (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = lmap f <<< map g

open Bifunctor {{...}} public

instance
  Bifunctor-Either : Bifunctor Either
  Bifunctor-Either .lmap f = either (left <<< f) right

  Bifunctor-Pair : Bifunctor Pair
  Bifunctor-Pair .lmap f (x , y) = (f x , y)

-------------------------------------------------------------------------------
-- Profunctor
-------------------------------------------------------------------------------

record Profunctor (p : Set -> Set -> Set) : Set where
  field
    overlap {{Functor-super}} : Functor (p a)
    lcmap : (b -> a) -> p a c -> p b c

  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lcmap f <<< map g

  arr : {{Category p}} -> (a -> b) -> p a b
  arr f = map f id

open Profunctor {{...}} public

instance
  Profunctor-Function : Profunctor Function
  Profunctor-Function .lcmap = _>>>_

-------------------------------------------------------------------------------
-- Applicative
-------------------------------------------------------------------------------

record Applicative (f : Set -> Set) : Set where
  infixl 4 _<*>_
  field
    overlap {{Functor-super}} : Functor f
    _<*>_ : f (a -> b) -> f a -> f b
    pure : a -> f a

  infixl 4 _<**>_
  _<**>_ : f a -> f (a -> b) -> f b
  xs <**> fs = (| xs # fs |)

  infixl 4 _*>_
  _*>_ : f a -> f b -> f b
  a *> b = (| (flip const) a b |)

  infixl 4 _<*_
  _<*_ : f a -> f b -> f a
  a <* b = (| const a b |)

  replicateA! : Nat -> f a -> f Unit
  replicateA! n0 fa = loop n0
    where
      loop : Nat -> f Unit
      loop 0 = pure tt
      loop (suc n) = fa *> loop n

  when : Bool -> f Unit -> f Unit
  when p x = if p then x else pure tt

  unless : Bool -> f Unit -> f Unit
  unless p x = if p then pure tt else x

open Applicative {{...}} public

{-# NON_TERMINATING #-}
forever : {{Applicative f}} -> f a -> f b
forever as = as *> forever as

instance
  Applicative-Function : Applicative (Function a)
  Applicative-Function .pure = const
  Applicative-Function ._<*>_ f g = \ x -> f x (g x)

  Applicative-Either : Applicative (Either a)
  Applicative-Either .pure = right
  Applicative-Either ._<*>_ = \ where
    (left a) _ -> left a
    (right f) -> map f

  Applicative-Pair : {{Monoid a}} -> Applicative (Pair a)
  Applicative-Pair .pure = (mempty ,_)
  Applicative-Pair ._<*>_ (u , f) (v , x) = (u <> v , f x)

  Applicative-Maybe : Applicative Maybe
  Applicative-Maybe .pure = just
  Applicative-Maybe ._<*>_ = \ where
    (just f) -> map f
    nothing _ -> nothing

  Applicative-List : Applicative List
  Applicative-List .pure = _:: []
  Applicative-List ._<*>_ = \ where
    [] _ -> []
    (f :: fs) xs -> (f <$> xs) <> (fs <*> xs)

  Applicative-IO : Applicative IO
  Applicative-IO .pure = pureIO
  Applicative-IO ._<*>_ = apIO

--------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

record Monad (m : Set -> Set) : Set where
  infixl 1 _>>=_
  field
    overlap {{Applicative-super}} : Applicative m
    _>>=_ : m a -> (a -> m b) -> m b

  infixl 1 _=<<_
  _=<<_ : (a -> m b) -> m a -> m b
  _=<<_ = flip _>>=_

  infixl 4 _>>_
  _>>_ : m a -> m b -> m b
  _>>_ = _*>_

  infixr 1 _<=<_
  _<=<_ : (b -> m c) -> (a -> m b) -> a -> m c
  _<=<_ f g x = g x >>= f

  infixr 1 _>=>_
  _>=>_ : (a -> m b) -> (b -> m c) -> a -> m c
  _>=>_ = flip _<=<_

  join : m (m a) -> m a
  join = _>>= id

open Monad {{...}} public

instance
  Monad-Function : Monad (Function a)
  Monad-Function ._>>=_ m k = \ a -> k (m a) a

  Monad-Either : Monad (Either a)
  Monad-Either ._>>=_ = \ where
    (left a) _ -> left a
    (right x) k -> k x

  Monad-Pair : {{Monoid a}} -> Monad (Pair a)
  Monad-Pair ._>>=_ (u , x) k = let (v , y) = k x in (u <> v , y)

  Monad-Maybe : Monad Maybe
  Monad-Maybe ._>>=_ = \ where
    nothing _ -> nothing
    (just x) k -> k x

  Monad-List : Monad List
  Monad-List ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x <> (xs >>= k)

  Monad-IO : Monad IO
  Monad-IO ._>>=_ = bindIO
