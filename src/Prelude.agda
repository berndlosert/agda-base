{-# OPTIONS --type-in-type #-}

module Prelude where

-------------------------------------------------------------------------------
-- Primitive types
-------------------------------------------------------------------------------

data Void : Set where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit)
  renaming (tt to unit)

open import Agda.Builtin.Bool public
  using (Bool)
  renaming (false to False)
  renaming (true to True)

data Ordering : Set where
  LT EQ GT : Ordering

open import Agda.Builtin.Nat public
  using (Nat)
  renaming (zero to Zero)
  renaming (suc to Suc)

data Nat1 : Set where
  Suc : Nat -> Nat1

open import Agda.Builtin.Int public
  using (Int)
  renaming (pos to Pos)
  renaming (negsuc to NegSuc)

open import Agda.Builtin.Float public
  using (Float)

open import Agda.Builtin.Char public
  using (Char)

open import Agda.Builtin.String public
  using (String)

open import Agda.Builtin.Equality public
  renaming (_≡_ to _===_)
  renaming (refl to Refl)

Function : Set -> Set -> Set
Function a b = a -> b

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b

{-# COMPILE GHC Either = data Either (Left | Right) #-}

open import Agda.Builtin.Sigma public
  renaming (Σ to DPair)
  renaming (_,_ to DPair:)

record Pair (a b : Set) : Set where
  constructor Pair:
  field
    fst : a
    snd : b

open Pair public

infixl 1 _,_
pattern _,_ x y = Pair: x y

{-# COMPILE GHC Pair = data (,) ((,)) #-}

open import Agda.Builtin.Maybe public
  using (Maybe)
  renaming (nothing to Nothing)
  renaming (just to Just)

open import Agda.Builtin.List public
  using (List)
  using ([])
  renaming (_∷_ to _::_)

infixr 5 _:|_
data List1 (a : Set) : Set where
  _:|_ : a -> List a -> List1 a

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
Assert False = Void
Assert True = Unit

bool : a -> a -> Bool -> a
bool x _ False = x
bool _ x True = x

infixr 0 if_then_else_
if_then_else_ : Bool -> a -> a -> a
if b then x else y = bool y x b

not : Bool -> Bool
not False = True
not True = False

infixr 2 _||_
_||_ : Bool -> Bool -> Bool
False || x = x
True || _ = True

infixr 3 _&&_
_&&_ : Bool -> Bool -> Bool
False && _ = False
True && x = x

-------------------------------------------------------------------------------
-- Nat primitives
-------------------------------------------------------------------------------

applyN : Nat -> (a -> a) -> a -> a
applyN 0 _ x = x
applyN (Suc n) f x = f (applyN n f x)

monus : Nat -> Nat -> Nat
monus = Agda.Builtin.Nat._-_

pred : Nat -> Nat
pred 0 = 0
pred (Suc n) = n

-------------------------------------------------------------------------------
-- Int primitives
-------------------------------------------------------------------------------

neg : Nat -> Int
neg 0 = Pos 0
neg (Suc n) = NegSuc n

diff : Nat -> Nat -> Int
diff m 0 = Pos m
diff Zero (Suc n) = NegSuc n
diff (Suc m) (Suc n) = diff m n

------------------------------------------------------------------------------
-- Either primitives
-------------------------------------------------------------------------------

either : (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x) = f x
either f g (Right x) = g x

mirror : Either a b -> Either b a
mirror = either Right Left

fromEither : Either a a -> a
fromEither (Left x) = x
fromEither (Right x) = x

isLeft : Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight : Either a b -> Bool
isRight (Left _) = False
isRight _ = True

fromLeft : {{Partial}} -> Either a b -> a
fromLeft (Left x) = x
fromLeft _ = undefined

fromRight : {{Partial}} -> Either a b -> b
fromRight (Right x) = x
fromRight _ = undefined

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
isJust (Just _) = True
isJust _ = False

isNothing : Maybe a -> Bool
isNothing (Just _) = False
isNothing _ = True

fromJust : {{Partial}} -> Maybe a -> a
fromJust (Just a) = a

maybe : b -> (a -> b) -> Maybe a -> b
maybe b f Nothing = b
maybe b f (Just a) = f a

fromMaybe : a -> Maybe a -> a
fromMaybe _ (Just x) = x
fromMaybe x Nothing = x

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
  x /= y = if x == y then False else True

  equating : (b -> a) -> b -> b -> Bool
  equating f x y = f x == f y

open Eq {{...}} public

instance
  Eq-Void : Eq Void
  Eq-Void ._==_ = \ ()

  Eq-Unit : Eq Unit
  Eq-Unit ._==_ unit unit = True

  Eq-Bool : Eq Bool
  Eq-Bool ._==_ = \ where
    True True -> True
    False False -> False
    _ _ -> False

  Eq-Ordering : Eq Ordering
  Eq-Ordering ._==_ = \ where
    LT LT -> True
    EQ EQ -> True
    GT GT -> True
    _ _ -> False

  Eq-Nat : Eq Nat
  Eq-Nat ._==_ = Agda.Builtin.Nat._==_

  Eq-Nat1 : Eq Nat1
  Eq-Nat1 ._==_ (Suc m) (Suc n) = m == n

  Eq-Int : Eq Int
  Eq-Int ._==_ = \ where
    (Pos m) (Pos n) -> m == n
    (NegSuc m) (NegSuc n) -> m == n
    _ _ -> False

  Eq-Float : Eq Float
  Eq-Float ._==_ = Agda.Builtin.Float.primFloatEquality

  Eq-Char : Eq Char
  Eq-Char ._==_ = Agda.Builtin.Char.primCharEquality

  Eq-String : Eq String
  Eq-String ._==_ = Agda.Builtin.String.primStringEquality

  Eq-Either : {{Eq a}} -> {{Eq b}} -> Eq (Either a b)
  Eq-Either ._==_ = \ where
    (Left x) (Left y) -> x == y
    (Right x) (Right y) -> x == y
    _ _ -> False

  Eq-Pair : {{Eq a}} -> {{Eq b}} -> Eq (Pair a b)
  Eq-Pair ._==_ (x , y) (w , z) = (x == w) && (y == z)

  Eq-Maybe : {{Eq a}} -> Eq (Maybe a)
  Eq-Maybe ._==_ = \ where
    Nothing Nothing -> True
    (Just x) (Just y) -> x == y
    _ _ -> False

  Eq-List : {{Eq a}} -> Eq (List a)
  Eq-List ._==_ = \ where
    [] [] -> True
    (x :: xs) (y :: ys) -> x == y && xs == ys
    _ _ -> False

  Eq-List1 : {{Eq a}} -> Eq (List1 a)
  Eq-List1 ._==_ (x :| xs) (y :| ys) = x == y && xs == ys

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
    LT -> True
    _ -> False

  infixl 4 _>_
  _>_ : a -> a -> Bool
  _>_ = flip _<_

  infixl 4 _<=_
  _<=_ : a -> a -> Bool
  x <= y = case compare x y of \ where
    GT -> False
    _ -> True

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
  Ord-Unit .compare unit unit = EQ

  Ord-Bool : Ord Bool
  Ord-Bool .compare False True = LT
  Ord-Bool .compare True False = GT
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

  Ord-Nat1 : Ord Nat1
  Ord-Nat1 .compare (Suc m) (Suc n) = compare m n

  Ord-Int : Ord Int
  Ord-Int .compare = \ where
    (Pos m) (Pos n) -> compare m n
    (NegSuc m) (NegSuc n) -> compare n m
    (Pos _) (NegSuc _) -> GT
    (NegSuc _) (Pos _) -> LT

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

  Ord-List1 : {{Ord a}} -> Ord (List1 a)
  Ord-List1 .compare (x :| xs) (y :| ys) =
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
  Ord-Maybe .compare Nothing Nothing = EQ
  Ord-Maybe .compare Nothing _ = LT
  Ord-Maybe .compare (Just x) (Just y) = compare x y
  Ord-Maybe .compare (Just _) _ = GT

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

  FromNat-Nat1 : FromNat Nat1
  FromNat-Nat1 .FromNatConstraint 0 = Void
  FromNat-Nat1 .FromNatConstraint _ = Unit
  FromNat-Nat1 .fromNat (Suc n) = Suc n

  FromNat-Int : FromNat Int
  FromNat-Int .FromNatConstraint _ = Unit
  FromNat-Int .fromNat n = Pos n

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
  ToNat-Nat1 : ToNat Nat1
  ToNat-Nat1 .ToNatConstraint _ = Unit
  ToNat-Nat1 .toNat (Suc n) = Suc n

  ToNat-Int : ToNat Int
  ToNat-Int .ToNatConstraint _ = Unit
  ToNat-Int .toNat (Pos n) = n
  ToNat-Int .toNat (NegSuc n) = 0

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
  Exp-Nat ._^_ m (Suc n) = m * m ^ n

  Divisor-Nat : Divisor Nat
  Divisor-Nat .divisor 0 = False
  Divisor-Nat .divisor _ = True

  Div-Nat : Div Nat
  Div-Nat .Divisor-super = Divisor-Nat
  Div-Nat ._/_ m (Suc n) = Agda.Builtin.Nat.div-helper 0 n m n

  Mod-Nat : Mod Nat
  Mod-Nat .Divisor-super = Divisor-Nat
  Mod-Nat ._%_ m (Suc n) = Agda.Builtin.Nat.mod-helper 0 n m n

  Add-Nat1 : Add Nat1
  Add-Nat1 ._+_ (Suc m) (Suc n) = Suc (Suc (m + n))

  Mul-Nat1 : Mul Nat1
  Mul-Nat1 ._*_ (Suc m) (Suc n) = Suc (m * n + m + n)

  Exp-Nat1 : Exp Nat1
  Exp-Nat1 .Power = Nat
  Exp-Nat1 ._^_ m 0 = Suc 0
  Exp-Nat1 ._^_ m (Suc n) = m * m ^ n

  Add-Int : Add Int
  Add-Int ._+_ = \ where
    (NegSuc m) (NegSuc n) -> NegSuc (Suc (m + n))
    (NegSuc m) (Pos n) -> diff n (Suc m)
    (Pos m) (NegSuc n) -> diff m (Suc n)
    (Pos m) (Pos n) -> Pos (m + n)

  Sub-Int : Sub Int
  Sub-Int .Diff = Int
  Sub-Int ._-_ = \ where
    m (Pos n) -> m + (neg n)
    m (NegSuc n) -> m + Pos (Suc n)

  Neg-Int : Neg Int
  Neg-Int .-_ = \ where
    (Pos 0) -> Pos 0
    (Pos (Suc n)) -> NegSuc n
    (NegSuc n) -> Pos (Suc n)

  Mul-Int : Mul Int
  Mul-Int ._*_ = \ where
    (Pos n) (Pos m) -> Pos (n * m)
    (NegSuc n) (NegSuc m) -> Pos (Suc n * Suc m)
    (Pos n) (NegSuc m) -> neg (n * Suc m)
    (NegSuc n) (Pos m) -> neg (Suc n * m)

  Exp-Int : Exp Int
  Exp-Int .Power = Nat
  Exp-Int ._^_ m 0 = Pos 0
  Exp-Int ._^_ m (Suc n) = m * m ^ n

  Divisor-Int : Divisor Int
  Divisor-Int .divisor (Pos 0) = False
  Divisor-Int .divisor _ = True

  Div-Int : Div Int
  Div-Int .Divisor-super = Divisor-Int
  Div-Int ._/_ = \ where
    (Pos m) (Pos n@(Suc _)) -> Pos (m / n)
    (Pos m) (NegSuc n) -> neg (m / Suc n)
    (NegSuc m) (Pos n@(Suc _)) -> neg (Suc m / n)
    (NegSuc m) (NegSuc n) -> Pos (Suc m / Suc n)

  Mod-Int : Mod Int
  Mod-Int .Divisor-super = Divisor-Int
  Mod-Int ._%_ = \ where
    (Pos m) (Pos n@(Suc _)) -> Pos (m % n)
    (Pos m) (NegSuc n) -> Pos (m % Suc n)
    (NegSuc m) (Pos n@(Suc _)) -> neg (Suc m % n)
    (NegSuc m) (NegSuc n) -> neg (Suc m % Suc n)

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
  Divisor-Float .divisor _ = True

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
  Semigroup-Unit ._<>_ unit unit = unit

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
  Semigroup-Either ._<>_ (Left _) x = x
  Semigroup-Either ._<>_ x _ = x

  Semigroup-Pair : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Pair a b)
  Semigroup-Pair ._<>_ (x , y) (w , z) = (x <> w , y <> z)

  Semigroup-Maybe : {{Semigroup a}} -> Semigroup (Maybe a)
  Semigroup-Maybe ._<>_ = \ where
    Nothing x -> x
    x Nothing -> x
    (Just x) (Just y) -> Just (x <> y)

  Semigroup-List : Semigroup (List a)
  Semigroup-List ._<>_ = \ where
    [] ys -> ys
    (x :: xs) ys -> x :: (xs <> ys)

  Semigroup-List1 : Semigroup (List1 a)
  Semigroup-List1 ._<>_ (x :| xs) (y :| ys) = x :| (xs <> y :: ys)

  Semigroup-IO : {{Semigroup a}} -> Semigroup (IO a)
  Semigroup-IO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Set) : Set where
  field
    overlap {{Semigroup-super}} : Semigroup a
    neutral : a

  mtimes : Nat -> a -> a
  mtimes 0 _ = neutral
  mtimes (Suc n) x = x <> mtimes n x

open Monoid {{...}} public

instance
  Monoid-Unit : Monoid Unit
  Monoid-Unit .neutral = unit

  Monoid-Ordering : Monoid Ordering
  Monoid-Ordering .neutral = EQ

  Monoid-String : Monoid String
  Monoid-String .neutral = ""

  Monoid-Function : {{Monoid b}} -> Monoid (a -> b)
  Monoid-Function .neutral = const neutral

  Monoid-Pair : {{Monoid a}} -> {{Monoid b}} -> Monoid (Pair a b)
  Monoid-Pair .neutral = (neutral , neutral)

  Monoid-Maybe : {{Semigroup a}} -> Monoid (Maybe a)
  Monoid-Maybe .neutral = Nothing

  Monoid-List : Monoid (List a)
  Monoid-List .neutral = []

  Monoid-IO : {{Monoid a}} -> Monoid (IO a)
  Monoid-IO .neutral = pureIO neutral

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
  ignore = unit <$_

  vacuous : f Void -> f a
  vacuous = map \ ()

open Functor {{...}} public

instance
  Functor-Function : Functor (Function a)
  Functor-Function .map = _<<<_

  Functor-Either : Functor (Either a)
  Functor-Either .map f = either Left (Right <<< f)

  Functor-Pair : Functor (Pair a)
  Functor-Pair .map f (x , y) = (x , f y)

  Functor-Maybe : Functor Maybe
  Functor-Maybe .map f = maybe Nothing (Just <<< f)

  Functor-List : Functor List
  Functor-List .map f = \ where
    [] -> []
    (x :: xs) -> f x :: map f xs

  Functor-List1 : Functor List1
  Functor-List1 .map f (x :| xs) = f x :| map f xs

  Functor-IO : Functor IO
  Functor-IO .map = mapIO

-------------------------------------------------------------------------------
-- Contravariant
-------------------------------------------------------------------------------

record Contravariant (f : Set -> Set) : Set where
  field cmap : (a -> b) -> f b -> f a

  phantom : {{Functor f}} -> f a -> f b
  phantom x = cmap (const unit) (map (const unit) x)

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
  Bifunctor-Either .lmap f = either (Left <<< f) Right

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
  xs <**> fs = (| _#_ xs fs |)

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
      loop 0 = pure unit
      loop (Suc n) = fa *> loop n

  when : Bool -> f Unit -> f Unit
  when p x = if p then x else pure unit

  unless : Bool -> f Unit -> f Unit
  unless p x = if p then pure unit else x

open Applicative {{...}} public

{-# NON_TERMINATING #-}
forever : {{Applicative f}} -> f a -> f b
forever as = as *> forever as

instance
  Applicative-Function : Applicative (Function a)
  Applicative-Function .pure = const
  Applicative-Function ._<*>_ f g = \ x -> f x (g x)

  Applicative-Either : Applicative (Either a)
  Applicative-Either .pure = Right
  Applicative-Either ._<*>_ = \ where
    (Left a) _ -> Left a
    (Right f) -> map f

  Applicative-Pair : {{Monoid a}} -> Applicative (Pair a)
  Applicative-Pair .pure = (neutral ,_)
  Applicative-Pair ._<*>_ (u , f) (v , x) = (u <> v , f x)

  Applicative-Maybe : Applicative Maybe
  Applicative-Maybe .pure = Just
  Applicative-Maybe ._<*>_ = \ where
    (Just f) -> map f
    Nothing _ -> Nothing

  Applicative-List : Applicative List
  Applicative-List .pure = _:: []
  Applicative-List ._<*>_ = \ where
    [] _ -> []
    (f :: fs) xs -> (f <$> xs) <> (fs <*> xs)

  Applicative-List1 : Applicative List1
  Applicative-List1 .pure x = x :| []
  Applicative-List1 ._<*>_ (f :| fs) (x :| xs) = f x :| (f :: fs <*> xs)

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
    (Left a) _ -> Left a
    (Right x) k -> k x

  Monad-Pair : {{Monoid a}} -> Monad (Pair a)
  Monad-Pair ._>>=_ (u , x) k = let (v , y) = k x in (u <> v , y)

  Monad-Maybe : Monad Maybe
  Monad-Maybe ._>>=_ = \ where
    Nothing _ -> Nothing
    (Just x) k -> k x

  Monad-List : Monad List
  Monad-List ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x <> (xs >>= k)

  Monad-List1 : Monad List1
  Monad-List1 ._>>=_ (x :| xs) k =
      case k x of \ where
        (y :| ys) ->
          let ys' = xs >>= k >>> toList
          in y :| (ys <> ys')
    where
      toList : List1 a -> List a
      toList (z :| zs) = z :: zs

  Monad-IO : Monad IO
  Monad-IO ._>>=_ = bindIO
