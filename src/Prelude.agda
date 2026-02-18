module Prelude where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

import Agda.Builtin.Bool
import Agda.Builtin.Char
import Agda.Builtin.Equality
import Agda.Builtin.Float
import Agda.Builtin.Int
import Agda.Builtin.IO
import Agda.Builtin.List
import Agda.Builtin.Maybe
import Agda.Builtin.Nat
import Agda.Builtin.Sigma
import Agda.Builtin.Strict
import Agda.Builtin.String
import Agda.Builtin.Unit
import Agda.Primitive

-------------------------------------------------------------------------------
-- Basic types
-------------------------------------------------------------------------------

open Agda.Primitive public
  renaming (Set to Type)
  using ()

data Void : Type where

open Agda.Builtin.Unit public
  renaming (⊤ to Unit)
  using (tt)

open Agda.Builtin.Bool public
  using (Bool)
  using (false)
  using (true)

data Ordering : Type where
  less equal greater : Ordering

{-# COMPILE GHC Ordering = data Ordering (LT | EQ | GT) #-}

open Agda.Builtin.Nat public
  using (Nat)
  using (suc)

data Nat1 : Type where
  suc : Nat -> Nat1

open Agda.Builtin.Int public
  using (Int)
  using (pos)
  using (negsuc)

open Agda.Builtin.Float public
  using (Float)

open Agda.Builtin.Char public
  using (Char)

open Agda.Builtin.String public
  using (String)

open Agda.Builtin.Equality public
  renaming (_≡_ to _===_)
  using (refl)

Function : Type -> Type -> Type
Function a b = a -> b

record Identity (a : Type) : Type where
  constructor asIdentity
  field runIdentity : a

open Identity public

record Const (a b : Type) : Type where
  constructor asConst
  field getConst : a

open Const public

open Agda.Builtin.Maybe public
  using (Maybe)
  using (nothing)
  using (just)

open Agda.Builtin.List public
  using (List)
  using ([])
  renaming (_∷_ to _::_)

data Either (a b : Type) : Type where
  left : a -> Either a b
  right : b -> Either a b

{-# COMPILE GHC Either = data Either (Left | Right) #-}

open Agda.Builtin.Sigma public
  renaming (Σ to Exists)
  renaming (_,_ to exists)

infixr 1 _,_
record Tuple (a b : Type) : Type where
  constructor _,_
  field
    fst : a
    snd : b

open Tuple public

{-# COMPILE GHC Tuple = data (,) ((,)) #-}

open Agda.Builtin.IO public
  using (IO)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c d l r s v : Type
    as : List Type
    f m : Type -> Type
    p : Type -> Type -> Type

-------------------------------------------------------------------------------
-- Dangerous
-------------------------------------------------------------------------------

postulate
  trustMe : a
  panic : String -> a

undefined : a
undefined = panic "Prelude.undefined"

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC panic = \ _ s -> error (Data.Text.unpack s) #-}

-------------------------------------------------------------------------------
-- Strictness functions
-------------------------------------------------------------------------------

infixr 0 _$!_
_$!_ : (a -> b) -> a -> b
f $! x = Agda.Builtin.Strict.primForce x f

seq : a -> b -> b
seq x y = (\ _ -> y) $! x

-------------------------------------------------------------------------------
-- Basic functions
-------------------------------------------------------------------------------

const : a -> b -> a
const x _ = x

flip : (a -> b -> c) -> b -> a -> c
flip f x y = f y x

infixr 0 _$_
_$_ : (a -> b) -> a -> b
f $ x = f x

infixl 1 _&_
_&_ : a -> (a -> b) -> b
_&_ x f = f x

case : a -> (a -> b) -> b
case x f = f x

_on_ : (b -> b -> c) -> (a -> b) -> a -> a -> c
_on_ f g x y = f (g x) (g y)

void : Void -> a
void = \ ()

! : a -> Unit
! _ = tt

applyN : (a -> a) -> Nat -> a -> a
applyN _ 0 x = x
applyN f (suc n) x = applyN f n (f $! x)

-------------------------------------------------------------------------------
-- Bool functions
-------------------------------------------------------------------------------

Assert : Bool -> Type
Assert false = Void
Assert true = Unit

infixr 0 if_then_else_
if_then_else_ : Bool -> a -> a -> a
if true then x else _ = x
if false then _ else x = x

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

_implies_ : Bool -> Bool -> Bool
_implies_ x y = not x || y

------------------------------------------------------------------------------
-- Either functions
-------------------------------------------------------------------------------

mirror : Either a b -> Either b a
mirror (left x) = right x
mirror (right x) = left x

uneither : Either a a -> a
uneither (left x) = x
uneither (right x) = x

either : (a -> c) -> (b -> c) -> Either a b -> c
either f g (left x) = f x
either f g (right x) = g x

fromEither : Either a b -> (a -> b) -> b
fromEither (left x) f = f x
fromEither (right x) _ = x

isLeft : Either a b -> Bool
isLeft (left _) = true
isLeft _ = false

isRight : Either a b -> Bool
isRight (right _) = true
isRight _ = false

-------------------------------------------------------------------------------
-- Tuple functions
-------------------------------------------------------------------------------

swap : Tuple a b -> Tuple b a
swap (x , y) = (y , x)

dup : a -> Tuple a a
dup x = (x , x)

-------------------------------------------------------------------------------
-- Maybe functions
-------------------------------------------------------------------------------

maybe : b -> (a -> b) -> Maybe a -> b
maybe x f nothing = x
maybe x f (just y) = f y

fromMaybe : Maybe a -> a -> a
fromMaybe (just x) _ = x
fromMaybe _ x = x

isJust : Maybe a -> Bool
isJust = maybe false (const true)

isNothing : Maybe a -> Bool
isNothing = maybe true (const false)

fromJust : (m : Maybe a) -> {{Assert (isJust m)}} -> a
fromJust (just x) = x

-------------------------------------------------------------------------------
-- IO functions
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
-- Uninhabited
-------------------------------------------------------------------------------

record Uninhabited (a : Type) : Type where
  field uninhabited : a -> Void

  absurd : a -> b
  absurd x = void (uninhabited x)

open Uninhabited {{...}} public

instance
  Uninhabited-Void : Uninhabited Void
  Uninhabited-Void .uninhabited = void

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

record Eq (a : Type) : Type where
  infix 4 _==_
  field _==_ : a -> a -> Bool

  infix 4 _/=_
  _/=_ : a -> a -> Bool
  x /= y = not (x == y)

open Eq {{...}} public

instance
  Eq-Void : Eq Void
  Eq-Void ._==_ = \ ()

  Eq-Unit : Eq Unit
  Eq-Unit ._==_ tt tt = true

  Eq-Bool : Eq Bool
  Eq-Bool ._==_ true true = true
  Eq-Bool ._==_ false false = true
  Eq-Bool ._==_ _ _ = false

  Eq-Ordering : Eq Ordering
  Eq-Ordering ._==_ less less = true
  Eq-Ordering ._==_ equal equal = true
  Eq-Ordering ._==_ greater greater = true
  Eq-Ordering ._==_ _ _ = false

  Eq-Nat : Eq Nat
  Eq-Nat ._==_ = Agda.Builtin.Nat._==_

  Eq-Nat1 : Eq Nat1
  Eq-Nat1 ._==_ (suc k) (suc m) = k == m

  Eq-Int : Eq Int
  Eq-Int ._==_ (pos m) (pos n) = m == n
  Eq-Int ._==_  (negsuc m) (negsuc n) = m == n
  Eq-Int ._==_  _ _ = false

  Eq-Float : Eq Float
  Eq-Float ._==_ = Agda.Builtin.Float.primFloatEquality

  Eq-Char : Eq Char
  Eq-Char ._==_ = Agda.Builtin.Char.primCharEquality

  Eq-String : Eq String
  Eq-String ._==_ = Agda.Builtin.String.primStringEquality

  Eq-Identity : {{Eq a}} -> Eq (Identity a)
  Eq-Identity {a} ._==_ x y = runIdentity x == runIdentity y

  Eq-Const : {{Eq a}} -> Eq (Const a b)
  Eq-Const ._==_ x y = getConst x == getConst y

  Eq-Either : {{Eq a}} -> {{Eq b}} -> Eq (Either a b)
  Eq-Either ._==_ (left x) (left y) = x == y
  Eq-Either ._==_ (right x) (right y) = x == y
  Eq-Either ._==_  _ _ = false

  Eq-Tuple : {{Eq a}} -> {{Eq b}} -> Eq (Tuple a b)
  Eq-Tuple ._==_ (x , y) (w , z) = (x == w) && (y == z)

  Eq-Maybe : {{Eq a}} -> Eq (Maybe a)
  Eq-Maybe ._==_ nothing nothing = true
  Eq-Maybe ._==_ (just x) (just y) = x == y
  Eq-Maybe ._==_ _ _ = false

  Eq-List : {{Eq a}} -> Eq (List a)
  Eq-List ._==_ [] [] = true
  Eq-List ._==_ (x :: xs) (y :: ys) = x == y && xs == ys
  Eq-List ._==_ _ _ = false

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

record Ord (a : Type) : Type where
  infixl 4 _<_
  field
    overlap {{Eq-super}} : Eq a
    _<_ : a -> a -> Bool

  infixl 4 _>_
  _>_ : a -> a -> Bool
  _>_ = flip _<_

  infixl 4 _<=_
  _<=_ : a -> a -> Bool
  x <= y = x == y || x < y

  infixl 4 _>=_
  _>=_ : a -> a -> Bool
  _>=_ = flip _<=_

  min : a -> a -> a
  min x y = if x < y then x else y

  max : a -> a -> a
  max x y = if x < y then y else x

  compare : a -> a -> Ordering
  compare x y = if x == y then equal else if x < y then less else greater

open Ord {{...}} public

order : (a -> a -> Ordering) -> Ord a
order cmp .Eq-super ._==_ x y = cmp x y == equal
order cmp ._<_ x y = cmp x y == less

instance
  Ord-Void : Ord Void
  Ord-Void ._<_ = \ ()

  Ord-Unit : Ord Unit
  Ord-Unit ._<_ _ _ = false

  Ord-Bool : Ord Bool
  Ord-Bool ._<_ false true = true
  Ord-Bool ._<_ _ _ = false

  Ord-Ordering : Ord Ordering
  Ord-Ordering ._<_ less equal = true
  Ord-Ordering ._<_ less greater = true
  Ord-Ordering ._<_ equal greater = true
  Ord-Ordering ._<_ _ _ = false

  Ord-Nat : Ord Nat
  Ord-Nat ._<_ = Agda.Builtin.Nat._<_

  Ord-Nat1 : Ord Nat1
  Ord-Nat1 ._<_ (suc k) (suc m) = k < m

  Ord-Int : Ord Int
  Ord-Int ._<_ (pos m) (pos n) = m < n
  Ord-Int ._<_ (negsuc m) (negsuc n) = n < m
  Ord-Int ._<_ (negsuc _) (pos _) = true
  Ord-Int ._<_  _ _ = false

  Ord-Float : Ord Float
  Ord-Float ._<_ = Agda.Builtin.Float.primFloatLess

  Ord-Char : Ord Char
  Ord-Char ._<_ c d =
    let toNat = Agda.Builtin.Char.primCharToNat
    in toNat c < toNat d

  Ord-Identity : {{Ord a}} -> Ord (Identity a)
  Ord-Identity {a} ._<_ x y = runIdentity x < runIdentity y

  Ord-Const : {{Ord a}} -> Ord (Const a b)
  Ord-Const ._<_ x y = getConst x < getConst y

  Ord-List : {{Ord a}} -> Ord (List a)
  Ord-List ._<_ [] [] = false
  Ord-List ._<_ [] (_ :: _) = true
  Ord-List ._<_ (_ :: _) [] = false
  Ord-List ._<_ (x :: xs) (y :: ys) = x < y && xs < ys

  Ord-String : Ord String
  Ord-String ._<_ s t =
    let toList = Agda.Builtin.String.primStringToList
    in toList s < toList t

  Ord-Tuple : {{Ord a}} -> {{Ord b}} -> Ord (Tuple a b)
  Ord-Tuple ._<_ (x , y) (w , z) =
    if x < w then true else if x == w then y < z else false

  Ord-Maybe : {{Ord a}} -> Ord (Maybe a)
  Ord-Maybe ._<_ nothing (just _) = true
  Ord-Maybe ._<_ (just x) (just y) = x < y
  Ord-Maybe ._<_ _ _ = false

-------------------------------------------------------------------------------
-- FromNat
-------------------------------------------------------------------------------

record FromNat (a : Type) : Type where
  field
    Constraint : Nat -> Type
    fromNat : (n : Nat) -> {{Constraint n}} -> a

open FromNat {{...}} public hiding (Constraint)

{-# BUILTIN FROMNAT fromNat #-}

instance
  FromNat-Nat : FromNat Nat
  FromNat-Nat .FromNat.Constraint _ = Unit
  FromNat-Nat .fromNat n = n

FromNat-Nat1 : FromNat Nat1
FromNat-Nat1 .FromNat.Constraint 0 = Void
FromNat-Nat1 .FromNat.Constraint _ = Unit
FromNat-Nat1 .fromNat (suc n) = suc n

FromNat-Int : FromNat Int
FromNat-Int .FromNat.Constraint _ = Unit
FromNat-Int .fromNat n = pos n

FromNat-Float : FromNat Float
FromNat-Float .FromNat.Constraint _ = Unit
FromNat-Float .fromNat n = Agda.Builtin.Float.primNatToFloat n

-------------------------------------------------------------------------------
-- ToNat
-------------------------------------------------------------------------------

record ToNat (a : Type) : Type where
  field toNat : a -> Nat

open ToNat {{...}} public

instance
  ToNat-Int : ToNat Int
  ToNat-Int .toNat (pos n) = n
  ToNat-Int .toNat (negsuc n) = 0

  ToNat-Nat1 : ToNat Nat1
  ToNat-Nat1 .toNat (suc m) = suc m

-------------------------------------------------------------------------------
-- FromNeg
-------------------------------------------------------------------------------

record FromNeg (a : Type) : Type where
  field neg : Nat -> a

open FromNeg {{...}} public

{-# BUILTIN FROMNEG neg #-}

instance
  FromNeg-Int : FromNeg Int
  FromNeg-Int .neg 0 = pos 0
  FromNeg-Int .neg (suc n) = negsuc n

  FromNeg-Float : FromNeg Float
  FromNeg-Float .neg n =
    Agda.Builtin.Float.primFloatNegate (Agda.Builtin.Float.primNatToFloat n)

-------------------------------------------------------------------------------
-- FromString
-------------------------------------------------------------------------------

record FromString (a : Type) : Type where
  field
    Constraint : String -> Type
    fromString : (s : String) -> {{Constraint s}} -> a

open FromString {{...}} public hiding (Constraint)

{-# BUILTIN FROMSTRING fromString #-}

instance
  FromString-String : FromString String
  FromString-String .FromString.Constraint _ = Unit
  FromString-String .fromString s = s

-------------------------------------------------------------------------------
-- Addable
-------------------------------------------------------------------------------

record Addable (a : Type) : Type where
  infixl 6 _+_
  field _+_ : a -> a -> a

open Addable {{...}} public

instance
  Addable-Type : Addable Type
  Addable-Type ._+_ = Either

  Addable-Function : {{Addable b}} -> Addable (a -> b)
  Addable-Function ._+_ f g x = f x + g x

  Addable-Void : Addable Void
  Addable-Void ._+_ = \ ()

  Addable-Unit : Addable Unit
  Addable-Unit ._+_ _ _ = tt

  Addable-Bool : Addable Bool
  Addable-Bool ._+_ = _||_

  Addable-Nat : Addable Nat
  Addable-Nat ._+_ = Agda.Builtin.Nat._+_

  Addable-Nat1 : Addable Nat1
  Addable-Nat1 ._+_ (suc m) (suc n) = suc (suc (m + n))

  Addable-Int : Addable Int
  Addable-Int ._+_ = \ where
      (negsuc m) (negsuc n) -> negsuc (suc (m + n))
      (negsuc m) (pos n) -> diff n (suc m)
      (pos m) (negsuc n) -> diff m (suc n)
      (pos m) (pos n) -> pos (m + n)
    where
      diff : Nat -> Nat -> Int
      diff m 0 = pos m
      diff 0 (suc n) = negsuc n
      diff (suc m) (suc n) = diff m n

  Addable-Float : Addable Float
  Addable-Float ._+_ = Agda.Builtin.Float.primFloatPlus

-------------------------------------------------------------------------------
-- Multiplicable
-------------------------------------------------------------------------------

record Multiplicable (a : Type) : Type where
  infixl 7 _*_
  field _*_ : a -> a -> a

open Multiplicable {{...}} public

instance
  Multiplicable-Type : Multiplicable Type
  Multiplicable-Type ._*_ = Tuple

  Multiplicable-Function : {{Multiplicable b}} -> Multiplicable (a -> b)
  Multiplicable-Function ._*_ f g x = f x * g x

  Multiplicable-Void : Multiplicable Void
  Multiplicable-Void ._*_ = \ ()

  Multiplicable-Unit : Multiplicable Unit
  Multiplicable-Unit ._*_ _ _ = tt

  Multiplicable-Bool : Multiplicable Bool
  Multiplicable-Bool ._*_ = _&&_

  Multiplicable-Nat : Multiplicable Nat
  Multiplicable-Nat ._*_ = Agda.Builtin.Nat._*_

  Multiplicable-Nat1 : Multiplicable Nat1
  Multiplicable-Nat1 ._*_ (suc m) (suc n) = suc (m * n + m + n)

  Multiplicable-Int : Multiplicable Int
  Multiplicable-Int ._*_ (pos n) (pos m) = pos (n * m)
  Multiplicable-Int ._*_ (negsuc n) (negsuc m) = pos (suc n * suc m)
  Multiplicable-Int ._*_ (pos n) (negsuc m) = neg (n * suc m)
  Multiplicable-Int ._*_ (negsuc n) (pos m) = neg (suc n * m)

  Multiplicable-Float : Multiplicable Float
  Multiplicable-Float ._*_ = Agda.Builtin.Float.primFloatTimes

-------------------------------------------------------------------------------
-- Negatable
-------------------------------------------------------------------------------

record Negatable (a : Type) : Type where
  field -_ : a -> a

open Negatable {{...}} public

instance
  Negatable-Int : Negatable Int
  Negatable-Int .-_ (pos 0) = pos 0
  Negatable-Int .-_ (pos (suc n)) = negsuc n
  Negatable-Int .-_ (negsuc n) = pos (suc n)

  Negatable-Float : Negatable Float
  Negatable-Float .-_ = Agda.Builtin.Float.primFloatNegate

-------------------------------------------------------------------------------
-- Subtractable
-------------------------------------------------------------------------------

record Subtractable (a : Type) : Type where
  infixl 6 _-_
  field
    _-_ : a -> a -> a

open Subtractable {{...}} public

instance
  Subtractable-Nat : Subtractable Nat
  Subtractable-Nat ._-_ 0 _ = 0
  Subtractable-Nat ._-_ (suc m) 0 = suc m
  Subtractable-Nat ._-_ (suc m) (suc n) = m - n

  Subtractable-Nat1 : Subtractable Nat1
  Subtractable-Nat1 ._-_ (suc m) (suc n) with m - n
  ... | 0 = suc 0
  ... | suc k = suc k

  Subtractable-Int : Subtractable Int
  Subtractable-Int ._-_ m n = m + (- n)

  Subtractable-Float : Subtractable Float
  Subtractable-Float ._-_ = Agda.Builtin.Float.primFloatMinus

-------------------------------------------------------------------------------
-- Exponentiable
-------------------------------------------------------------------------------

record Exponentiable (a : Type) : Type where
  infixr 8 _^_
  field
    Power : Type
    _^_ : a -> Power -> a

open Exponentiable {{...}} public

instance
  Exponentiable-Type : Exponentiable Type
  Exponentiable-Type .Power = Nat
  Exponentiable-Type ._^_ a 0 = Void
  Exponentiable-Type ._^_ a (suc 0) = a
  Exponentiable-Type ._^_ a (suc n) = a * (a ^ n)

  Exponentiable-Nat : Exponentiable Nat
  Exponentiable-Nat .Power = Nat
  Exponentiable-Nat ._^_ m 0 = 1
  Exponentiable-Nat ._^_ m (suc n) = m * (m ^ n)

  Exponentiable-Int : Exponentiable Int
  Exponentiable-Int .Power = Nat
  Exponentiable-Int ._^_ m 0 = pos 0
  Exponentiable-Int ._^_ m (suc n) = m * m ^ n

  Exponentiable-Float : Exponentiable Float
  Exponentiable-Float .Power = Float
  Exponentiable-Float ._^_ = Agda.Builtin.Float.primFloatPow

-------------------------------------------------------------------------------
-- Integral
-------------------------------------------------------------------------------

record Integral (a : Type) : Type where
  field
    div : a -> a -> a
    mod : a -> a -> a

open Integral {{...}} public

instance
  Integral-Nat : Integral Nat
  Integral-Nat .div m 0 = 0
  Integral-Nat .div m (suc n) = Agda.Builtin.Nat.div-helper 0 n m n
  Integral-Nat .mod m 0 = m
  Integral-Nat .mod m (suc n) = Agda.Builtin.Nat.mod-helper 0 n m n

  Integral-Int : Integral Int
  Integral-Int .div (pos m) (pos n@(suc _)) = pos (div m n)
  Integral-Int .div (pos m) (negsuc n) = neg (div m (suc n))
  Integral-Int .div (negsuc m) (pos n@(suc _)) = neg (div (suc m) n)
  Integral-Int .div (negsuc m) (negsuc n) = pos (div (suc m) (suc n))
  Integral-Int .div _ (pos 0) = pos 0
  Integral-Int .mod (pos m) (pos n@(suc _)) = pos (mod m n)
  Integral-Int .mod (pos m) (negsuc n) = pos (mod m (suc n))
  Integral-Int .mod (negsuc m) (pos n@(suc _)) = neg (mod (suc m) n)
  Integral-Int .mod (negsuc m) (negsuc n) = neg (mod (suc m) (suc n))
  Integral-Int .mod m (pos 0) = m

-------------------------------------------------------------------------------
-- Fractional
-------------------------------------------------------------------------------

record Fractional (a : Type) : Type where
  infixl 7 _/_
  field _/_ : a -> a -> a

open Fractional {{...}} public

instance
  Fractional-Float : Fractional Float
  Fractional-Float ._/_ x y = Agda.Builtin.Float.primFloatDiv x y

-------------------------------------------------------------------------------
-- Semigroupoid
-------------------------------------------------------------------------------

record Semigroupoid {k : Type} (p : k -> k -> Type) : Type where
  infixr 9 _<<<_
  field _<<<_ : {a b c : k} -> p b c -> p a b -> p a c

  infixr 9 _>>>_
  _>>>_ : {a b c : k} -> p a b -> p b c -> p a c
  _>>>_ = flip _<<<_

open Semigroupoid {{...}} public

instance
  Semigroupoid-Function : Semigroupoid Function
  Semigroupoid-Function ._<<<_ g f x = g (f x)

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

record Category {k : Type} (p : k -> k -> Type) : Type where
  field
    overlap {{Semigroupoid-super}} : Semigroupoid p
    id : {a : k} -> p a a

open Category {{...}} public

instance
  Category-Function : Category Function
  Category-Function .id x = x

-------------------------------------------------------------------------------
-- Semigroup
-------------------------------------------------------------------------------

record Semigroup (a : Type) : Type where
  infixr 5 _<>_
  field _<>_ : a -> a -> a

  stimes : Nat1 -> a -> a
  stimes (suc n) x = applyN (x <>_) n x

open Semigroup {{...}} public

instance
  Semigroup-Void : Semigroup Void
  Semigroup-Void ._<>_ = \ ()

  Semigroup-Unit : Semigroup Unit
  Semigroup-Unit ._<>_ tt tt = tt

  Semigroup-Ordering : Semigroup Ordering
  Semigroup-Ordering ._<>_ less _ = less
  Semigroup-Ordering ._<>_ equal y = y
  Semigroup-Ordering ._<>_ greater _ = greater

  Semigroup-String : Semigroup String
  Semigroup-String ._<>_ = Agda.Builtin.String.primStringAppend

  Semigroup-Function : {{Semigroup b}} -> Semigroup (a -> b)
  Semigroup-Function ._<>_ f g x = f x <> g x

  Semigroup-Identity : {{Semigroup a}} -> Semigroup (Identity a)
  Semigroup-Identity {a} ._<>_ x y = asIdentity (runIdentity x <> runIdentity y)

  Semigroup-Const : {{Semigroup a}} -> Semigroup (Const a b)
  Semigroup-Const ._<>_ x y = asConst (getConst x <> getConst y)

  Semigroup-Maybe : {{Semigroup a}} -> Semigroup (Maybe a)
  Semigroup-Maybe ._<>_ nothing x = x
  Semigroup-Maybe ._<>_ x nothing = x
  Semigroup-Maybe ._<>_ (just x) (just y) = just (x <> y)

  Semigroup-List : Semigroup (List a)
  Semigroup-List ._<>_ [] ys = ys
  Semigroup-List ._<>_ (x :: xs) ys = x :: (xs <> ys)

  Semigroup-Either : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Either a b)
  Semigroup-Either ._<>_ (left _) x = x
  Semigroup-Either ._<>_ x _ = x

  Semigroup-Tuple : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Tuple a b)
  Semigroup-Tuple ._<>_ (x , y) (w , z) = (x <> w , y <> z)

  Semigroup-IO : {{Semigroup a}} -> Semigroup (IO a)
  Semigroup-IO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| x <> y |)

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Type) : Type where
  field
    overlap {{Semigroup-super}} : Semigroup a
    mempty : a

  mtimes : Nat -> a -> a
  mtimes n x = applyN (x <>_) n mempty

open Monoid {{...}} public

instance
  Monoid-Unit : Monoid Unit
  Monoid-Unit .mempty = tt

  Monoid-Ordering : Monoid Ordering
  Monoid-Ordering .mempty = equal

  Monoid-String : Monoid String
  Monoid-String .mempty = ""

  Monoid-Function : {{Monoid b}} -> Monoid (a -> b)
  Monoid-Function .mempty = const mempty

  Monoid-Identity : {{Monoid a}} -> Monoid (Identity a)
  Monoid-Identity .mempty = asIdentity mempty

  Monoid-Const : {{Monoid a}} -> Monoid (Const a b)
  Monoid-Const .mempty = asConst mempty

  Monoid-Maybe : {{Semigroup a}} -> Monoid (Maybe a)
  Monoid-Maybe .mempty = nothing

  Monoid-List : Monoid (List a)
  Monoid-List .mempty = []

  Monoid-Tuple : {{Monoid a}} -> {{Monoid b}} -> Monoid (Tuple a b)
  Monoid-Tuple .mempty = (mempty , mempty)

  Monoid-IO : {{Monoid a}} -> Monoid (IO a)
  Monoid-IO .mempty = pureIO mempty

-------------------------------------------------------------------------------
-- Functor
-------------------------------------------------------------------------------

record Functor (f : Type -> Type) : Type where
  field map : (a -> b) -> f a -> f b

  infixl 4 _<$>_
  _<$>_ : (a -> b) -> f a -> f b
  _<$>_ = map

  infixl 1 _<&>_
  _<&>_ : f a -> (a -> b) -> f b
  _<&>_ = flip map

  infixl 4 _<$_
  _<$_ : b -> f a -> f b
  _<$_ = map <<< const

  infixl 4 _$>_
  _$>_ : f a -> b -> f b
  _$>_ = flip _<$_

open Functor {{...}} public

instance
  Functor-Function : Functor (Function a)
  Functor-Function .map = _<<<_

  Functor-Identity : Functor Identity
  Functor-Identity .map f = asIdentity <<< f <<< runIdentity

  Functor-Const : Functor (Const a)
  Functor-Const .map _ = asConst <<< getConst

  Functor-Maybe : Functor Maybe
  Functor-Maybe .map f = maybe nothing (just <<< f)

  Functor-List : Functor List
  Functor-List .map f [] = []
  Functor-List .map f (x :: xs) = f x :: map f xs

  Functor-Either : Functor (Either a)
  Functor-Either .map f = either left (right <<< f)

  Functor-Tuple : Functor (Tuple a)
  Functor-Tuple .map f (x , y) = (x , f y)

  Functor-IO : Functor IO
  Functor-IO .map = mapIO

-------------------------------------------------------------------------------
-- Applicative
-------------------------------------------------------------------------------

record Applicative (f : Type -> Type) : Type where
  infixl 4 _<*>_
  field
    overlap {{Functor-super}} : Functor f
    _<*>_ : f (a -> b) -> f a -> f b
    pure : a -> f a

  infixl 4 _*>_
  _*>_ : f a -> f b -> f b
  x *> y = (| (flip const) x y |)

  infixl 4 _<*_
  _<*_ : f a -> f b -> f a
  x <* y = (| const x y |)

  when : Bool -> f Unit -> f Unit
  when b x = if b then x else pure tt

  unless : Bool -> f Unit -> f Unit
  unless b = when (not b)

  replicateA' : Nat -> f a -> f Unit
  replicateA' 0 _ = pure tt
  replicateA' (suc n) x = x *> replicateA' n x

  forever : f a -> f b
  forever x = x *> forever x

open Applicative {{...}} public

instance
  Applicative-Function : Applicative (Function a)
  Applicative-Function .pure = const
  Applicative-Function ._<*>_ f g x = f x (g x)

  Applicative-Identity : Applicative Identity
  Applicative-Identity .pure = asIdentity
  Applicative-Identity ._<*>_ f = asIdentity <<< runIdentity f <<< runIdentity

  Applicative-Const : {{Monoid a}} -> Applicative (Const a)
  Applicative-Const .pure _ = asConst mempty
  Applicative-Const ._<*>_ f x = asConst (getConst f <> getConst x)

  Applicative-Maybe : Applicative Maybe
  Applicative-Maybe .pure = just
  Applicative-Maybe ._<*>_ (just f) = map f
  Applicative-Maybe ._<*>_ nothing _ = nothing

  Applicative-List : Applicative List
  Applicative-List .pure = _:: []
  Applicative-List ._<*>_ [] _ = []
  Applicative-List ._<*>_ (f :: fs) xs  = (f <$> xs) <> (fs <*> xs)

  Applicative-Either : Applicative (Either a)
  Applicative-Either .pure = right
  Applicative-Either ._<*>_ (left x) _ = left x
  Applicative-Either ._<*>_ (right f) = map f

  Applicative-Tuple : {{Monoid a}} -> Applicative (Tuple a)
  Applicative-Tuple .pure = (mempty ,_)
  Applicative-Tuple ._<*>_ (u , f) (v , x) = (u <> v , f x)

  Applicative-IO : Applicative IO
  Applicative-IO .pure = pureIO
  Applicative-IO ._<*>_ = apIO

-------------------------------------------------------------------------------
-- Alternative
-------------------------------------------------------------------------------

record Alternative (f : Type -> Type) : Type where
  infixl 3 _<|>_
  field
    overlap {{Applicative-super}} : Applicative f
    _<|>_ : f a -> f a -> f a
    azero : f a

  guarded : (a -> Bool) -> a -> f a
  guarded p x = if p x then pure x else azero

  guard : Bool -> f Unit
  guard b = guarded (const b) tt

open Alternative {{...}} public

instance
  Alternative-Maybe : Alternative Maybe
  Alternative-Maybe .azero = nothing
  Alternative-Maybe ._<|>_ nothing r = r
  Alternative-Maybe ._<|>_ l _ = l

  Alternative-List : Alternative List
  Alternative-List .azero = mempty
  Alternative-List ._<|>_ = _<>_

-------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

record Monad (m : Type -> Type) : Type where
  infixl 1 _>>=_
  field
    overlap {{Applicative-super}} : Applicative m
    _>>=_ : m a -> (a -> m b) -> m b

  caseM : m a -> (a -> m b) -> m b
  caseM = _>>=_

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

  liftM : (a -> b) -> m a -> m b
  liftM f x = do
    y <- x
    pure (f y)

  ap : m (a -> b) -> m a -> m b
  ap f x = do
    g <- f
    y <- x
    pure (g y)

open Monad {{...}} public

instance
  Monad-Function : Monad (Function a)
  Monad-Function ._>>=_ f g x = g (f x) x

  Monad-Identity : Monad Identity
  Monad-Identity ._>>=_ x k = k (runIdentity x)

  Monad-Maybe : Monad Maybe
  Monad-Maybe ._>>=_ nothing _ = nothing
  Monad-Maybe ._>>=_ (just x) k = k x

  Monad-List : Monad List
  Monad-List ._>>=_ [] k = []
  Monad-List ._>>=_ (x :: xs) k = k x <> (xs >>= k)    
    
  Monad-Either : Monad (Either a)
  Monad-Either ._>>=_ (left x) _ = left x
  Monad-Either ._>>=_ (right x) k = k x

  Monad-Tuple : {{Monoid a}} -> Monad (Tuple a)
  Monad-Tuple ._>>=_ (u , x) k = let (v , y) = k x in (u <> v , y)

  Monad-IO : Monad IO
  Monad-IO ._>>=_ = bindIO
