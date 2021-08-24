{-# OPTIONS --type-in-type --no-import-sorts #-}

module Prelude where

-------------------------------------------------------------------------------
-- Primitive types
-------------------------------------------------------------------------------

open import Agda.Primitive public
  renaming (Set to Type)

data Void : Type where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit)
  renaming (tt to unit)

open import Agda.Builtin.Bool public
  using (Bool)
  renaming (false to False)
  renaming (true to True)

data Ordering : Type where
  LT EQ GT : Ordering

open import Agda.Builtin.Nat public
  using (Nat)
  renaming (zero to Zero)
  renaming (suc to Suc)

data Fin : Nat -> Type where
  Zero : {n : Nat} -> Fin (Suc n)
  Suc : {n : Nat} -> Fin n -> Fin (Suc n)

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

Function : Type -> Type -> Type
Function a b = a -> b

data Either (a b : Type) : Type where
  Left : a -> Either a b
  Right : b -> Either a b

{-# COMPILE GHC Either = data Either (Left | Right) #-}

open import Agda.Builtin.Sigma public
  renaming (Σ to DPair)
  renaming (_,_ to DPair:)

record Pair (a b : Type) : Type where
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

open import Agda.Builtin.IO public
  using (IO)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c d r s : Type
    f m : Type -> Type
    p : Type -> Type -> Type

-------------------------------------------------------------------------------
-- Dangerous primitives
-------------------------------------------------------------------------------

postulate
  trustMe : a
  error : String -> a

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC error = \ _ s -> error (Data.Text.unpack s) #-}

undefined : a
undefined = error "Prelude.undefined"

-------------------------------------------------------------------------------
-- Function primitives
-------------------------------------------------------------------------------

the : (a : Type) -> a -> a
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

Assert : Bool -> Type
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

-----------------------------------------------------------------------------------------
-- Nat primitives
-----------------------------------------------------------------------------------------

applyN : (a -> a) -> Nat -> a -> a
applyN _ 0 x = x
applyN f (Suc n) x = f (applyN f n x)

private
  natEquality : Nat -> Nat -> Bool
  natEquality = Agda.Builtin.Nat._==_

  natLessThan : Nat -> Nat -> Bool
  natLessThan = Agda.Builtin.Nat._<_

  natPlus : Nat -> Nat -> Nat
  natPlus = Agda.Builtin.Nat._+_

  natMinus : Nat -> Nat -> Nat
  natMinus = Agda.Builtin.Nat._-_

  natNegate : Nat -> Int
  natNegate 0 = Pos 0
  natNegate (Suc n) = NegSuc n

  natTimes : Nat -> Nat -> Nat
  natTimes = Agda.Builtin.Nat._*_

  natDivAux : (k m n j : Nat) -> Nat
  natDivAux = Agda.Builtin.Nat.div-helper

  natModAux : (k m n j : Nat) -> Nat
  natModAux = Agda.Builtin.Nat.mod-helper

  natDiv : Nat -> Nat -> Nat
  natDiv m (Suc n) = natDivAux Zero n m n
  natDiv _ _ = undefined

  natMod : Nat -> Nat -> Nat
  natMod m (Suc n) = natModAux Zero n m n
  natMod _ _ = undefined

  natShow : Nat -> String
  natShow = Agda.Builtin.String.primShowNat

-------------------------------------------------------------------------------
-- Fin primitives
-------------------------------------------------------------------------------

private
  finToNat : {n : Nat} -> Fin n -> Nat
  finToNat Zero = Zero
  finToNat (Suc n) = Suc (finToNat n)

  natToFin : (m n : Nat) -> Maybe (Fin n)
  natToFin Zero (Suc j) = Just Zero
  natToFin (Suc m) (Suc n) =
    case natToFin m n of \ where
      (Just k') -> Just (Suc k')
      Nothing -> Nothing
  natToFin _ _ = Nothing

  finEquality : {n : Nat} -> Fin n -> Fin n -> Bool
  finEquality Zero Zero = True
  finEquality (Suc n) (Suc m) = finEquality n m
  finEquality _ _ = False

  finLessThan : {n : Nat} -> Fin n -> Fin n -> Bool
  finLessThan _ Zero = False
  finLessThan Zero (Suc _) = True
  finLessThan (Suc n) (Suc m) = finLessThan n m

  finPlus : {n : Nat} -> Fin n -> Fin n -> Fin n
  finPlus {n} k m =
    case natToFin (natMod (natPlus (finToNat k) (finToNat m)) n) n of \ where
      (Just k') -> k'
      Nothing -> undefined

  finNegate : {n : Nat} -> Fin n -> Fin n
  finNegate {n} m =
    case natToFin (natMinus n (finToNat m)) n of \ where
      (Just k) -> k
      Nothing -> undefined

  finMinus : {n : Nat} -> Fin n -> Fin n -> Fin n
  finMinus k m = finPlus k (finNegate m)

  finTimes : {n : Nat} -> Fin n -> Fin n -> Fin n
  finTimes {n} k m =
    case natToFin (natMod (natTimes (finToNat k) (finToNat m)) n) n of \ where
      (Just k') -> k'
      Nothing -> undefined

-------------------------------------------------------------------------------
-- Int primitives
-------------------------------------------------------------------------------

private
  intLessThan : Int -> Int -> Bool
  intLessThan (Pos m) (Pos n) = natLessThan m n
  intLessThan (NegSuc m) (NegSuc n) = natLessThan n m
  intLessThan (NegSuc _) (Pos _) = True
  intLessThan (Pos _) (NegSuc _) = False

  intNegate : Int -> Int
  intNegate = \ where
    (Pos Zero) -> Pos Zero
    (Pos (Suc n)) -> NegSuc n
    (NegSuc n) -> Pos (Suc n)

  intMinus : Nat -> Nat -> Int
  intMinus m Zero = Pos m
  intMinus Zero (Suc n) = NegSuc n
  intMinus (Suc m) (Suc n) = intMinus m n

  intPlus : Int -> Int -> Int
  intPlus (NegSuc m) (NegSuc n) = NegSuc (Suc (natPlus m n))
  intPlus (NegSuc m) (Pos n) = intMinus n (Suc m)
  intPlus (Pos m) (NegSuc n) = intMinus m (Suc n)
  intPlus (Pos m) (Pos n) = Pos (natPlus m n)

  intTimes : Int -> Int -> Int
  intTimes = \ where
    (Pos n) (Pos m) -> Pos (natTimes n m)
    (NegSuc n) (NegSuc m) -> Pos (natTimes (Suc n) (Suc m))
    (Pos n) (NegSuc m) -> natNegate (natTimes n (Suc m))
    (NegSuc n) (Pos m) -> natNegate (natTimes (Suc n) m)

  intDiv : Int -> Int -> Int
  intDiv = \ where
    (Pos m) (Pos n) -> Pos (natDiv m n)
    (Pos m) (NegSuc n) -> natNegate (natDiv m (Suc n))
    (NegSuc m) (Pos n) -> natNegate (natDiv (Suc m) n)
    (NegSuc m) (NegSuc n) -> Pos (natDiv (Suc m) (Suc n))

  intMod : Int -> Int -> Int
  intMod = \ where
    (Pos m) (Pos n) -> Pos (natMod m n)
    (Pos m) (NegSuc n) -> Pos (natMod m (Suc n))
    (NegSuc m) (Pos n) -> natNegate (natMod (Suc m) n)
    (NegSuc m) (NegSuc n) -> natNegate (natMod (Suc m) (Suc n))

  intShow : Int -> String
  intShow = Agda.Builtin.Int.primShowInteger

-------------------------------------------------------------------------------
-- Float primitives
-------------------------------------------------------------------------------

private
  floatEq : Float -> Float -> Bool
  floatEq = Agda.Builtin.Float.primFloatEquality

  floatLessThan : Float -> Float -> Bool
  floatLessThan =  Agda.Builtin.Float.primFloatLess

  floatPlus : Float -> Float -> Float
  floatPlus = Agda.Builtin.Float.primFloatPlus

  floatNegate : Float -> Float
  floatNegate = Agda.Builtin.Float.primFloatNegate

  floatMinus : Float -> Float -> Float
  floatMinus = Agda.Builtin.Float.primFloatMinus

  floatTimes : Float -> Float -> Float
  floatTimes = Agda.Builtin.Float.primFloatTimes

  floatDiv : Float -> Float -> Float
  floatDiv = Agda.Builtin.Float.primFloatDiv

  natToFloat : Nat -> Float
  natToFloat = Agda.Builtin.Float.primNatToFloat

  floatShow : Float -> String
  floatShow = Agda.Builtin.Float.primShowFloat

NaN : Float
NaN = floatDiv 0.0 0.0

Infinity -Infinity : Float
Infinity = floatDiv 1.0 0.0
-Infinity = floatNegate Infinity

sqrt : Float -> Float
sqrt = Agda.Builtin.Float.primFloatSqrt

round : Float -> Maybe Int
round = Agda.Builtin.Float.primFloatRound

floor : Float -> Maybe Int
floor = Agda.Builtin.Float.primFloatFloor

ceil : Float -> Maybe Int
ceil = Agda.Builtin.Float.primFloatCeiling

exp : Float -> Float
exp = Agda.Builtin.Float.primFloatExp

log : Float -> Float
log = Agda.Builtin.Float.primFloatLog

sin : Float -> Float
sin = Agda.Builtin.Float.primFloatSin

cos : Float -> Float
cos = Agda.Builtin.Float.primFloatCos

tan : Float -> Float
tan = Agda.Builtin.Float.primFloatTan

asin : Float -> Float
asin = Agda.Builtin.Float.primFloatASin

acos : Float -> Float
acos = Agda.Builtin.Float.primFloatACos

atan : Float -> Float
atan = Agda.Builtin.Float.primFloatATan

atan2 : Float -> Float -> Float
atan2 = Agda.Builtin.Float.primFloatATan2

sinh : Float -> Float
sinh = Agda.Builtin.Float.primFloatSinh

cosh : Float -> Float
cosh = Agda.Builtin.Float.primFloatCosh

tanh : Float -> Float
tanh = Agda.Builtin.Float.primFloatTanh

asinh : Float -> Float
asinh = Agda.Builtin.Float.primFloatASinh

acosh : Float -> Float
acosh = Agda.Builtin.Float.primFloatACosh

atanh : Float -> Float
atanh = Agda.Builtin.Float.primFloatATanh

-------------------------------------------------------------------------------
-- Char primitives
-------------------------------------------------------------------------------

private
  charEq : Char -> Char -> Bool
  charEq = Agda.Builtin.Char.primCharEquality

  natToChar : Nat -> Char
  natToChar = Agda.Builtin.Char.primNatToChar

  charShow : Char -> String
  charShow = Agda.Builtin.String.primShowChar

minChar maxChar : Char
minChar = '\NUL'
maxChar = '\1114111'

isLower : Char -> Bool
isLower = Agda.Builtin.Char.primIsLower

isDigit : Char -> Bool
isDigit = Agda.Builtin.Char.primIsDigit

isAlpha : Char -> Bool
isAlpha = Agda.Builtin.Char.primIsAlpha

isSpace : Char -> Bool
isSpace = Agda.Builtin.Char.primIsSpace

isAscii : Char -> Bool
isAscii = Agda.Builtin.Char.primIsAscii

isLatin1 : Char -> Bool
isLatin1 = Agda.Builtin.Char.primIsLatin1

isPrint : Char -> Bool
isPrint = Agda.Builtin.Char.primIsPrint

isHexDigit : Char -> Bool
isHexDigit = Agda.Builtin.Char.primIsHexDigit

toUpper : Char -> Char
toUpper = Agda.Builtin.Char.primToUpper

toLower : Char -> Char
toLower = Agda.Builtin.Char.primToLower

ord : Char -> Nat
ord = Agda.Builtin.Char.primCharToNat

chr : Fin (Suc (ord maxChar)) -> Char
chr n = Agda.Builtin.Char.primNatToChar (finToNat n)

-------------------------------------------------------------------------------
-- String primitives
-------------------------------------------------------------------------------

private
  stringEq : String -> String -> Bool
  stringEq = Agda.Builtin.String.primStringEquality

  stringAppend : String -> String -> String
  stringAppend = Agda.Builtin.String.primStringAppend

  stringShow : String -> String
  stringShow = Agda.Builtin.String.primShowString

pack : List Char -> String
pack = Agda.Builtin.String.primStringFromList

unpack : String -> List Char
unpack = Agda.Builtin.String.primStringToList

-------------------------------------------------------------------------------
-- Either primitives
-------------------------------------------------------------------------------

either : (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left a) = f a
either f g (Right b) = g b

mirror : Either a b -> Either b a
mirror = either Right Left

fromEither : Either a a -> a
fromEither (Left a) = a
fromEither (Right a) = a

isLeft : Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight : Either a b -> Bool
isRight (Left _) = False
isRight _ = True

fromLeft : (x : Either a b) -> {{Assert $ isLeft x}} -> a
fromLeft (Left a) = a

fromRight : (x : Either a b) -> {{Assert $ isRight x}} -> b
fromRight (Right b) = b

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

fromJust : (x : Maybe a) -> {{Assert $ isJust x}} -> a
fromJust (Just a) = a

maybe : b -> (a -> b) -> Maybe a -> b
maybe b f Nothing = b
maybe b f (Just a) = f a

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

record Eq (a : Type) : Type where
  infix 4 _==_
  field _==_ : a -> a -> Bool

  infix 4 _/=_
  _/=_ : a -> a -> Bool
  x /= y = if x == y then False else True

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
  Eq-Nat ._==_ = natEquality

  Eq-Fin : {n : Nat} -> Eq (Fin n)
  Eq-Fin ._==_ = finEquality

  Eq-Int : Eq Int
  Eq-Int ._==_ = \ where
    (Pos m) (Pos n) -> m == n
    (NegSuc m) (NegSuc n) -> m == n
    _ _ -> False

  Eq-Float : Eq Float
  Eq-Float ._==_ = floatEq

  Eq-Char : Eq Char
  Eq-Char ._==_ = charEq

  Eq-String : Eq String
  Eq-String ._==_ = stringEq

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

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

record Ord (a : Type) : Type where
  infixl 4 _<_
  field
    overlap {{Eq-super}} : Eq a
    _<_ : a -> a -> Bool

  compare : a -> a -> Ordering
  compare x y = if x < y then LT else if x == y then EQ else GT

  infixl 4 _<=_
  _<=_ : a -> a -> Bool
  x <= y = if x < y then True else if x == y then True else False

  infixl 4 _>_
  _>_ : a -> a -> Bool
  _>_ = flip _<_

  infixl 4 _>=_
  _>=_ : a -> a -> Bool
  _>=_ = flip _<=_

  min : a -> a -> a
  min x y = if x < y then x else y

  max : a -> a -> a
  max x y = if x < y then y else x

  comparing : (b -> a) -> b -> b -> Ordering
  comparing p x y = compare (p x) (p y)

open Ord {{...}} public

instance
  Ord-Void : Ord Void
  Ord-Void ._<_ = \ ()

  Ord-Unit : Ord Unit
  Ord-Unit ._<_ unit unit = False

  Ord-Bool : Ord Bool
  Ord-Bool ._<_ = \ where
    False True -> True
    _ _ -> False

  Ord-Ordering : Ord Ordering
  Ord-Ordering ._<_ = \ where
    LT EQ -> True
    LT LT -> True
    EQ GT -> True
    _ _ -> False

  Ord-Nat : Ord Nat
  Ord-Nat ._<_ = natLessThan

  Ord-Fin : {n : Nat} -> Ord (Fin n)
  Ord-Fin ._<_ = finLessThan

  Ord-Int : Ord Int
  Ord-Int ._<_ = intLessThan

  Ord-Float : Ord Float
  Ord-Float ._<_ = floatLessThan

  Ord-Char : Ord Char
  Ord-Char ._<_ x y = ord x < ord y

  Ord-List : {{Ord a}} -> Ord (List a)
  Ord-List ._<_ = \ where
    (x :: xs) (y :: ys) -> x < y || (x == y && xs < ys)
    _ _ -> False

  Ord-String : Ord String
  Ord-String ._<_ l r = unpack l < unpack r

  Ord-Pair : {{Ord a}} -> {{Ord b}} -> Ord (Pair a b)
  Ord-Pair ._<_ (x , y) (w , z) = x < w || (x == w && y < z)

  Ord-Maybe : {{Ord a}} -> Ord (Maybe a)
  Ord-Maybe ._<_ = \ where
    _ Nothing -> False
    Nothing _ -> True
    (Just x) (Just y) -> x < y

-------------------------------------------------------------------------------
-- FromNat, ToNat, FromNeg, ToFloat
-------------------------------------------------------------------------------

record FromNat (a : Type) : Type where
  field
    FromNatConstraint : Nat -> Type
    fromNat : (n : Nat) -> {{FromNatConstraint n}} -> a

open FromNat {{...}} public

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY FromNat.fromNat _ n = fromNat n #-}

record ToNat (a : Type) : Type where
  field
    ToNatConstraint : a -> Type
    toNat : (x : a) -> {{ToNatConstraint x}} -> Nat

open ToNat {{...}} public

record FromNeg (a : Type) : Type where
  field
    FromNegConstraint : Nat -> Type
    fromNeg : (n : Nat) -> {{FromNegConstraint n}} -> a

open FromNeg {{...}} public

{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY FromNeg.fromNeg _ n = fromNeg n #-}

record ToFloat (a : Type) : Type where
  field toFloat : a -> Float

open ToFloat {{...}} public

instance
  FromNat-Nat : FromNat Nat
  FromNat-Nat .FromNatConstraint _ = Unit
  FromNat-Nat .fromNat n = n

  FromNat-Fin : {n : Nat} -> FromNat (Fin (Suc n))
  FromNat-Fin {n} .FromNatConstraint m = Assert (m <= n)
  FromNat-Fin {n} .fromNat m {{p}} = go m n {p}
    where
      go : (m n : Nat) {_ : Assert $ m <= n} -> Fin (Suc n)
      go Zero _ = Zero
      go (Suc m) (Suc n) {p} = Suc (go m n {p})

  FromNat-Int : FromNat Int
  FromNat-Int .FromNatConstraint _ = Unit
  FromNat-Int .fromNat n = Pos n

  FromNat-Float : FromNat Float
  FromNat-Float .FromNatConstraint _ = Unit
  FromNat-Float .fromNat n = natToFloat n

  FromNat-Type : FromNat Type
  FromNat-Type .FromNatConstraint _ = Unit
  FromNat-Type .fromNat 0 = Void
  FromNat-Type .fromNat 1 = Unit
  FromNat-Type .fromNat (Suc n) = Either (fromNat 1) (fromNat n)

  ToNat-Nat : ToNat Nat
  ToNat-Nat .ToNatConstraint _ = Unit
  ToNat-Nat .toNat n = n

  ToNat-Fin : {n : Nat} -> ToNat (Fin n)
  ToNat-Fin .ToNatConstraint _ = Unit
  ToNat-Fin .toNat n = finToNat n

  ToNat-Int : ToNat Int
  ToNat-Int .ToNatConstraint n = Assert (n >= 0)
  ToNat-Int .toNat (Pos n) = n

  FromNeg-Int : FromNeg Int
  FromNeg-Int .FromNegConstraint _ = Unit
  FromNeg-Int .fromNeg n = natNegate n

  FromNeg-Float : FromNeg Float
  FromNeg-Float .FromNegConstraint _ = Unit
  FromNeg-Float .fromNeg n = floatNegate (natToFloat n)

  ToFloat-Nat : ToFloat Nat
  ToFloat-Nat .toFloat = natToFloat

  ToFloat-Int : ToFloat Int
  ToFloat-Int .toFloat (Pos n) = natToFloat n
  ToFloat-Int .toFloat (NegSuc n) = floatMinus -1.0 (natToFloat n)

-------------------------------------------------------------------------------
-- Num
-------------------------------------------------------------------------------

record Num (a : Type) : Type where
  infixl 6 _+_
  infixl 6 _-_
  infixl 7 _*_
  field
    overlap {{super}} : FromNat a
    nonzero : a -> Bool
    _+_ : a -> a -> a
    _-_ : a -> a -> a
    _*_ : a -> a -> a

  Nonzero : a -> Type
  Nonzero x = Assert (nonzero x)

  FromZero : (b : Type) -> {{a === b}} -> Type
  FromZero _ = FromNatConstraint {{super}} 0

  FromOne : (b : Type) -> {{a === b}} -> Type
  FromOne _ = FromNatConstraint {{super}} 1

  times : {{FromZero _}} -> Nat -> a -> a
  times 0 _ = 0
  times (Suc n) x = times n x + x

  infixr 8 _^_
  _^_ : {{FromOne _}} -> a -> Nat -> a
  a ^ 0 = 1
  a ^ (Suc n) = a ^ n * a

open Num {{...}} public

instance
  Num-Nat : Num Nat
  Num-Nat .nonzero 0 = False
  Num-Nat .nonzero _ = True
  Num-Nat ._+_ = natPlus
  Num-Nat ._-_ = natMinus
  Num-Nat ._*_ = natTimes

  Num-Fin : {n : Nat} -> Num (Fin (Suc n))
  Num-Fin .nonzero Zero = False
  Num-Fin .nonzero _ = True
  Num-Fin ._+_ = finPlus
  Num-Fin ._-_ = finMinus
  Num-Fin ._*_ = finTimes

  Num-Int : Num Int
  Num-Int .nonzero (Pos 0) = False
  Num-Int .nonzero _ = True
  Num-Int ._+_ = intPlus
  Num-Int ._-_ m n = m + intNegate n
  Num-Int ._*_ = intTimes

  Num-Float : Num Float
  Num-Float .nonzero x = if x == 0.0 then False else True
  Num-Float ._+_ = floatPlus
  Num-Float ._-_ = floatMinus
  Num-Float ._*_ = floatTimes

-------------------------------------------------------------------------------
-- Signed
-------------------------------------------------------------------------------

record Signed (a : Type) : Type where
  field
    overlap {{Num-super}} : Num a
    overlap {{FromNeg-super}} : FromNeg a
    -_ : a -> a
    abs : a -> a
    signum : a -> a

open Signed {{...}} public

instance
  Signed-Int : Signed Int
  Signed-Int .-_ = intNegate
  Signed-Int .abs n@(Pos _) = n
  Signed-Int .abs (NegSuc n) = Pos (Suc n)
  Signed-Int .signum n@(Pos 0) = n
  Signed-Int .signum (Pos _) = Pos 1
  Signed-Int .signum (NegSuc _) = NegSuc 0

  Signed-Float : Signed Float
  Signed-Float .-_ = floatNegate
  Signed-Float .abs x = if x < 0 then - x else x
  Signed-Float .signum x = case compare x 0 of \ where
    LT -> -1
    EQ -> 0
    GT -> 1

-------------------------------------------------------------------------------
-- Integral
-------------------------------------------------------------------------------

record Integral (a : Type) : Type where
  field
    overlap {{super}} : Num a
    div : (x y : a) -> {{Nonzero y}} -> a
    mod : (x y : a) -> {{Nonzero y}} -> a

open Integral {{...}} public

instance
  Integral-Nat : Integral Nat
  Integral-Nat .div x y = natDiv x y
  Integral-Nat .mod x y = natMod x y

  Integral-Int : Integral Int
  Integral-Int .div x y = intDiv x y
  Integral-Int .mod x y = intMod x y

-------------------------------------------------------------------------------
-- Fractional
-------------------------------------------------------------------------------

record Fractional (a : Type) : Type where
  field
    overlap {{super}} : Num a
    _/_ : (x y : a) -> {{Nonzero y}} -> a

open Fractional {{...}} public

instance
  Fractional-Float : Fractional Float
  Fractional-Float ._/_ x y = floatDiv x y

-------------------------------------------------------------------------------
-- Semigroup
-------------------------------------------------------------------------------

record Semigroup (a : Type) : Type where
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
  Semigroup-String ._<>_ = stringAppend

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

  Semigroup-IO : {{Semigroup a}} -> Semigroup (IO a)
  Semigroup-IO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Type) : Type where
  field
    overlap {{Semigroup-super}} : Semigroup a
    neutral : a

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

record Category (p : Type -> Type -> Type) : Type where
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

record Functor (f : Type -> Type) : Type where
  field map : (a -> b) -> f a -> f b

  infixl 4 _<$>_
  _<$>_ : (a -> b) -> f a -> f b
  _<$>_ = map

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

  Functor-IO : Functor IO
  Functor-IO .map = mapIO

-------------------------------------------------------------------------------
-- Contravariant
-------------------------------------------------------------------------------

record Contravariant (f : Type -> Type) : Type where
  field cmap : (a -> b) -> f b -> f a

  phantom : {{Functor f}} -> f a -> f b
  phantom x = cmap (const unit) (map (const unit) x)

open Contravariant {{...}} public

-------------------------------------------------------------------------------
-- Bifunctor
-------------------------------------------------------------------------------

record Bifunctor (p : Type -> Type -> Type) : Type where
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

record Profunctor (p : Type -> Type -> Type) : Type where
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

record Applicative (f : Type -> Type) : Type where
  infixl 4 _<*>_
  field
    overlap {{Functor-super}} : Functor f
    _<*>_ : f (a -> b) -> f a -> f b
    pure : a -> f a

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
    (f :: fs) xs -> (map f xs) <> (fs <*> xs)

  Applicative-IO : Applicative IO
  Applicative-IO .pure = pureIO
  Applicative-IO ._<*>_ = apIO

--------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

record Monad (m : Type -> Type) : Type where
  infixl 1 _>>=_
  field
    overlap {{Applicative-super}} : Applicative m
    _>>=_ : m a -> (a -> m b) -> m b

  infixl 4 _>>_
  _>>_ : m a -> m b -> m b
  _>>_ = _*>_

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

  Monad-IO : Monad IO
  Monad-IO ._>>=_ = bindIO

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

record Enum (a : Type) : Type where
  field
    {{Ord-super}} : Ord a
    SucConstraint : a -> Type
    PredConstraint : a -> Type
    suc : (x : a) -> {{SucConstraint x}} -> a
    pred : (x : a) -> {{PredConstraint x}} -> a
    enumFromTo : a -> a -> List a

open Enum {{...}} public

instance
  Enum-Nat : Enum Nat
  Enum-Nat .SucConstraint _ = Unit
  Enum-Nat .PredConstraint 0 = Void
  Enum-Nat .PredConstraint _ = Unit
  Enum-Nat .suc x = Suc x
  Enum-Nat .pred (Suc n) = n
  Enum-Nat .enumFromTo m n =
      let k = max (m - n) (n - m)
      in go k m n
    where
      go : Nat -> Nat -> Nat -> List Nat
      go 0 m _ = m :: []
      go (Suc k) m n =
        let m' = if m < n then m + 1 else m - 1
        in m :: go k m' n

  Enum-Int : Enum Int
  Enum-Int .SucConstraint _ = Unit
  Enum-Int .PredConstraint _ = Unit
  Enum-Int .suc n = n + 1
  Enum-Int .pred n = n - 1
  Enum-Int .enumFromTo m n =
    case m - n of \ where
      (Pos k) -> (\ i -> Pos i + n) <$> enumFromTo k 0
      (NegSuc k) -> (\ i -> Pos i + m) <$> enumFromTo 0 (Suc k)

  Enum-Char : Enum Char
  Enum-Char .SucConstraint c = Assert (c < maxChar)
  Enum-Char .PredConstraint c = Assert (c > minChar)
  Enum-Char .suc c = natToChar $ suc (ord c)
  Enum-Char .pred c = natToChar $ pred (ord c) {{trustMe}}
  Enum-Char .enumFromTo c d = natToChar <$> enumFromTo (ord c) (ord d)

-------------------------------------------------------------------------------
-- Bounded
-------------------------------------------------------------------------------

record Bounded (a : Type) : Type where
  field
    overlap {{Ord-super}} : Ord a
    minBound : a
    maxBound : a

open Bounded {{...}} public

instance
  Bounded-Char : Bounded Char
  Bounded-Char .minBound = minChar
  Bounded-Char .maxBound = maxChar

  Bounded-Float : Bounded Float
  Bounded-Float .minBound = Infinity
  Bounded-Float .maxBound = -Infinity

-------------------------------------------------------------------------------
-- Show
-------------------------------------------------------------------------------

ShowS : Type
ShowS = String -> String

record Show (a : Type) : Type where
  field showsPrec : Nat -> a -> ShowS

  shows : a -> ShowS
  shows = showsPrec 0

  show : a -> String
  show x = shows x ""

open Show {{...}} public

showString : String -> ShowS
showString = _<>_

showParen : Bool -> ShowS -> ShowS
showParen b p = if b then showString "(" <<< p <<< showString ")" else p

appPrec appPrec+1 : Nat
appPrec = 10
appPrec+1 = 11

instance
  Show-Void : Show Void
  Show-Void .showsPrec _ ()

  Show-Unit : Show Unit
  Show-Unit .showsPrec _ unit = showString "unit"

  Show-Bool : Show Bool
  Show-Bool .showsPrec _ b = showString (if b then "True" else "False")

  Show-Ordering : Show Ordering
  Show-Ordering .showsPrec _ = \ where
    LT -> showString "LT"
    EQ -> showString "EQ"
    GT -> showString "GT"

  Show-Nat : Show Nat
  Show-Nat .showsPrec _ = showString <<< natShow

  Show-Fin : {n : Nat} -> Show (Fin n)
  Show-Fin .showsPrec _ = showString <<< natShow <<< finToNat

  Show-Int : Show Int
  Show-Int .showsPrec _ = showString <<< intShow

  Show-Float : Show Float
  Show-Float .showsPrec _ = showString <<< floatShow

  Show-Char : Show Char
  Show-Char .showsPrec _ = showString <<< charShow

  Show-String : Show String
  Show-String .showsPrec _ = showString <<< stringShow

  Show-Function : Show (Function a b)
  Show-Function .showsPrec _ _ = showString "<function>"

  Show-Pair : {{Show a}} -> {{Show b}} -> Show (Pair a b)
  Show-Pair .showsPrec d (x , y) = showString "(" <<< showsPrec d x
    <<< showString " , " <<< showsPrec d y <<< showString ")"

  Show-Either : {{Show a}} -> {{Show b}} -> Show (Either a b)
  Show-Either .showsPrec d = \ where
    (Left x) -> showParen (d > appPrec)
      (showString "Left " <<< showsPrec appPrec+1 x)
    (Right x) -> showParen (d > appPrec)
      (showString "Right " <<< showsPrec appPrec+1 x)

  Show-Maybe : {{Show a}} -> Show (Maybe a)
  Show-Maybe .showsPrec d = \ where
    (Just x) -> showParen (d > appPrec)
      (showString "Just " <<< showsPrec appPrec+1 x)
    Nothing -> showString "Nothing"

  Show-List : {{Show a}} -> Show (List a)
  Show-List .showsPrec _ [] = showString "[]"
  Show-List .showsPrec d (x :: xs) =
      showString "[" <<< content <<< showString "]"
    where
      content : ShowS
      content = showsPrec d x <<< go xs
        where
          go : {{Show a}} -> List a -> ShowS
          go [] = showString ""
          go (y :: ys) = showString ", " <<< showsPrec d y <<< go ys
