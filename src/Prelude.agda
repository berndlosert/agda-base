{-# OPTIONS --type-in-type #-}

module Prelude where

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c d r s : Set
    f m : Set -> Set

-------------------------------------------------------------------------------
-- Primitive types and type constructors
-------------------------------------------------------------------------------

data Void : Set where

record Unit : Set where
  instance constructor unit

{-# BUILTIN UNIT Unit #-}
{-# COMPILE GHC Unit = data () (()) #-}

data Bool : Set where
  False True : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE False #-}
{-# BUILTIN TRUE True #-}

data Nat : Set where
  Zero : Nat
  Suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data Int : Set where
  Pos : Nat -> Int
  NegSuc : Nat -> Int

{-# BUILTIN INTEGER Int #-}
{-# BUILTIN INTEGERPOS Pos #-}
{-# BUILTIN INTEGERNEGSUC NegSuc #-}

postulate Float : Set

{-# BUILTIN FLOAT Float #-}

postulate Char : Set

{-# BUILTIN CHAR Char #-}

postulate String : Set

{-# BUILTIN STRING String #-}

infix 4 _===_
data _===_ {a : Set} (x : a) : a -> Set where
 instance Refl : x === x

{-# BUILTIN EQUALITY _===_ #-}

Function : Set -> Set -> Set
Function a b = a -> b

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b

{-# COMPILE GHC Either = data Either (Left | Right) #-}

infixl 1 _,_
record Tuple (a b : Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b

open Tuple public

{-# COMPILE GHC Tuple = data (,) ((,)) #-}

data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just : a -> Maybe a

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

infixr 5 _::_
data List (a : Set) : Set where
  [] : List a
  _::_ : a -> List a -> List a

{-# BUILTIN LIST List #-}

postulate IO : Set -> Set

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

-------------------------------------------------------------------------------
-- Wrappers
-------------------------------------------------------------------------------

record Identity (a : Set) : Set where
  constructor Identity:
  field runIdentity : a

open Identity public

record Const (a b : Set) : Set where
  constructor Const:
  field getConst : a

open Const public

record Endo (a : Set) : Set where
  constructor Endo:
  field appEndo : a -> a

open Endo public

-------------------------------------------------------------------------------
-- Primitive functions and operations
-------------------------------------------------------------------------------

postulate
  believeMe : a
  error : String -> a

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC error = \ _ s -> error (Data.Text.unpack s) #-}

undefined : a
undefined = error "Prelude.undefined"

const : a -> b -> a
const x _ = x

flip : (a -> b -> c) -> b -> a -> c
flip f x y = f y x

infixr 0 _$_
_$_ : (a -> b) -> a -> b
f $ x = f x

infixl 1 _#_
_#_ : a -> (a -> b) -> b
_#_ = flip _$_

case_of_ : a -> (a -> b) -> b
case_of_ = _#_

Assert : Bool -> Set
Assert False = Void
Assert True = Unit

infixr 0 if_then_else_
if_then_else_ : Bool -> a -> a -> a
if True then x else _ = x
if False then _ else x = x

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

natrec : a -> (Nat -> a -> a) -> Nat -> a
natrec x _ 0 = x
natrec x h n@(Suc n-1) = h n-1 (natrec x h n-1)

applyN : (a -> a) -> Nat -> a -> a
applyN f n x = natrec x (const f) n

private
  natEquality : Nat -> Nat -> Bool
  natEquality Zero Zero = True
  natEquality (Suc n) (Suc m) = natEquality n m
  natEquality _ _ = False

  natLessThan : Nat -> Nat -> Bool
  natLessThan _ Zero = False
  natLessThan Zero (Suc _) = True
  natLessThan (Suc n) (Suc m) = natLessThan n m

  natPlus : Nat -> Nat -> Nat
  natPlus Zero m = m
  natPlus (Suc n) m = Suc (natPlus n m)

  natMinus : Nat -> Nat -> Nat
  natMinus n Zero = n
  natMinus Zero (Suc m) = Zero
  natMinus (Suc n) (Suc m) = natMinus n m

  natTimes : Nat -> Nat -> Nat
  natTimes Zero _ = Zero
  natTimes (Suc n) m = natPlus m (natTimes n m)

  natDivAux : (k m n j : Nat) -> Nat
  natDivAux k m Zero j = k
  natDivAux k m (Suc n) Zero = natDivAux (Suc k) m n m
  natDivAux k m (Suc n) (Suc j) = natDivAux k m n j

  natModAux : (k m n j : Nat) -> Nat
  natModAux k m  Zero j = k
  natModAux k m (Suc n) Zero = natModAux 0 m n m
  natModAux k m (Suc n) (Suc j) = natModAux (Suc k) m n j

{-# BUILTIN NATEQUALS natEquality #-}
{-# BUILTIN NATLESS natLessThan #-}
{-# BUILTIN NATPLUS natPlus #-}
{-# BUILTIN NATMINUS natMinus #-}
{-# BUILTIN NATTIMES natTimes #-}
{-# BUILTIN NATDIVSUCAUX natDivAux #-}
{-# BUILTIN NATMODSUCAUX natModAux #-}

pred : Nat -> Nat
pred 0 = 0
pred (Suc n) = n

neg : Nat -> Int
neg 0 = Pos 0
neg (Suc n) = NegSuc n

isPos : Int -> Bool
isPos (Pos _) = True
isPos _ = False

private
  primitive
    primFloatNumericalEquality : Float -> Float -> Bool
    primFloatNumericalLess : Float -> Float -> Bool
    primNatToFloat : Nat -> Float
    primFloatPlus : Float -> Float -> Float
    primFloatMinus : Float -> Float -> Float
    primFloatTimes : Float -> Float -> Float
    primFloatNegate : Float -> Float
    primFloatDiv : Float -> Float -> Float
    primFloatSqrt : Float -> Float
    primRound : Float -> Int
    primFloor : Float -> Int
    primCeiling : Float -> Int
    primExp : Float -> Float
    primLog : Float -> Float
    primSin : Float -> Float
    primCos : Float -> Float
    primTan : Float -> Float
    primASin : Float -> Float
    primACos : Float -> Float
    primATan : Float -> Float
    primATan2 : Float -> Float -> Float

sqrt = primFloatSqrt
round = primRound
floor = primFloor
ceil = primCeiling
exp = primExp
log = primLog
sin = primSin
cos = primCos
tan = primTan
asin = primASin
acos = primACos
atan = primATan
atan2 = primATan2

private
  primitive
    primCharEquality : Char -> Char -> Bool
    primIsLower : Char -> Bool
    primIsDigit : Char -> Bool
    primIsAlpha : Char -> Bool
    primIsSpace : Char -> Bool
    primIsAscii : Char -> Bool
    primIsLatin1 : Char -> Bool
    primIsPrint : Char -> Bool
    primIsHexDigit : Char -> Bool
    primToUpper : Char -> Char
    primToLower : Char -> Char
    primCharToNat : Char -> Nat
    primNatToChar : Nat -> Char

isLower = primIsLower
isDigit = primIsDigit
isAlpha = primIsAlpha
isSpace = primIsSpace
isAscii = primIsAscii
isLatin1 = primIsLatin1
isPrint = primIsPrint
isHexDigit = primIsHexDigit
toUpper = primToUpper
toLower = primToLower
ord = primCharToNat
chr = primNatToChar

private
  primitive
    primStringEquality : String -> String -> Bool
    primStringToList : String -> List Char
    primStringFromList : List Char -> String
    primStringAppend : String -> String -> String

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

lefts : List (Either a b) -> List a
lefts [] = []
lefts (Left a :: xs) = a :: lefts xs
lefts (_ :: xs) = lefts xs

rights : List (Either a b) -> List b
rights [] = []
rights (Right b :: xs) = b :: rights xs
rights (_ :: xs) = rights xs

partitionEithers : List (Either a b) -> Tuple (List a) (List b)
partitionEithers xs = (lefts xs , rights xs)

tuple : (a -> b) -> (a -> c) -> a -> Tuple b c
tuple f g x = (f x , g x)

swap : Tuple a b -> Tuple b a
swap = tuple snd fst

dupe : a -> Tuple a a
dupe x = (x , x)

uncurry : (a -> b -> c) -> Tuple a b -> c
uncurry f (x , y) = f x y

curry : (Tuple a b -> c) -> a -> b -> c
curry f x y = f (x , y)

apply : Tuple (a -> b) a -> b
apply (f , x) = f x

isJust : Maybe a -> Bool
isJust (Just _) = True
isJust _ = False

isNothing : Maybe a -> Bool
isNothing (Just _) = False
isNothing _ = True

fromJust : (m : Maybe a) {{_ : Assert (isJust m)}} -> a
fromJust (Just x) = x

maybe : b -> (a -> b) -> Maybe a -> b
maybe b f Nothing = b
maybe b f (Just a) = f a

maybeToLeft : b -> Maybe a -> Either a b
maybeToLeft b = maybe (Right b) Left

maybeToRight : b -> Maybe a -> Either b a
maybeToRight b = maybe (Left b) Right

leftToMaybe : Either a b -> Maybe a
leftToMaybe = either Just (const Nothing)

rightToMaybe : Either a b -> Maybe b
rightToMaybe = either (const Nothing) Just

pattern [_] x = x :: []

listrec : b -> (a -> List a -> b -> b) -> List a -> b
listrec b f [] = b
listrec b f (a :: as) = f a as (listrec b f as)

maybeToList : Maybe a -> List a
maybeToList Nothing = []
maybeToList (Just x) = x :: []

listToMaybe : List a -> Maybe a
listToMaybe [] = Nothing
listToMaybe (x :: _) = Just x

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
-- Packed
-------------------------------------------------------------------------------

record Packed (s a : Set) : Set where
  field
    pack : List a -> s
    unpack : s -> List a

open Packed {{...}} public

instance
  Packed-String-Char : Packed String Char
  Packed-String-Char .pack = primStringFromList
  Packed-String-Char .unpack = primStringToList

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

record Eq (a : Set) : Set where
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

  Eq-Nat : Eq Nat
  Eq-Nat ._==_ = natEquality

  Eq-Int : Eq Int
  Eq-Int ._==_ = \ where
    (Pos m) (Pos n) -> m == n
    (NegSuc m) (NegSuc n) -> m == n
    _ _ -> False

  Eq-Float : Eq Float
  Eq-Float ._==_ = primFloatNumericalEquality

  Eq-Char : Eq Char
  Eq-Char ._==_ = primCharEquality

  Eq-String : Eq String
  Eq-String ._==_ = primStringEquality

  Eq-Either : {{_ : Eq a}} {{_ : Eq b}} -> Eq (Either a b)
  Eq-Either ._==_ = \ where
    (Left x) (Left y) -> x == y
    (Right x) (Right y) -> x == y
    _ _ -> False

  Eq-Tuple : {{_ : Eq a}} {{_ : Eq b}} -> Eq (Tuple a b)
  Eq-Tuple ._==_ (x , y) (w , z) = (x == w) && (y == z)

  Eq-Maybe : {{_ : Eq a}} -> Eq (Maybe a)
  Eq-Maybe ._==_ = \ where
    Nothing Nothing -> True
    (Just x) (Just y) -> x == y
    _ _ -> False

  Eq-List : {{_ : Eq a}} -> Eq (List a)
  Eq-List ._==_ = \ where
    [] [] -> True
    (x :: xs) (y :: ys) -> x == y && xs == ys
    _ _ -> False

  Eq-Identity : {{_ : Eq a}} -> Eq (Identity a)
  Eq-Identity ._==_ (Identity: x) (Identity: y) = x == y

  Eq-Const : {{_ : Eq a}} -> Eq (Const a b)
  Eq-Const ._==_ (Const: x) (Const: y) = x == y

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (a : Set) : Set where
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

  Ord-Nat : Ord Nat
  Ord-Nat ._<_ = natLessThan

  Ord-Int : Ord Int
  Ord-Int ._<_ = \ where
    (Pos m) (Pos n) -> m < n
    (NegSuc m) (NegSuc n) -> m > n
    (NegSuc _) (Pos _) -> True
    (Pos _) (NegSuc _) -> False

  Ord-Float : Ord Float
  Ord-Float ._<_ = primFloatNumericalLess

  Ord-Char : Ord Char
  Ord-Char ._<_ x y = ord x < ord y

  Ord-List : {{_ : Ord a}} -> Ord (List a)
  Ord-List ._<_ = \ where
    (x :: xs) (y :: ys) -> x < y || (x == y && xs < ys)
    _ _ -> False

  Ord-String : Ord String
  Ord-String ._<_ l r = toList l < toList r
    where toList = primStringToList

  Ord-Tuple : {{_ : Ord a}} {{_ : Ord b}} -> Ord (Tuple a b)
  Ord-Tuple ._<_ (x , y) (w , z) = x < w || (x == w && y < z)

  Ord-Maybe : {{_ : Ord a}} -> Ord (Maybe a)
  Ord-Maybe ._<_ = \ where
    _ Nothing -> False
    Nothing _ -> True
    (Just x) (Just y) -> x < y

  Ord-Identity : {{_ : Ord a}} -> Ord (Identity a)
  Ord-Identity ._<_ (Identity: x) (Identity: y) = x < y

  Ord-Const : {{_ : Ord a}} -> Ord (Const a b)
  Ord-Const ._<_ (Const: x) (Const: y) = x < y

-------------------------------------------------------------------------------
-- FromNat, ToNat, FromNeg, ToFloat
-------------------------------------------------------------------------------

record FromNat (a : Set) : Set where
  field
    FromNatConstraint : Nat -> Set
    fromNat : (n : Nat) {{_ : FromNatConstraint n}} -> a

open FromNat {{...}} public

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY FromNat.fromNat _ n = fromNat n #-}

record ToNat (a : Set) : Set where
  field
    ToNatConstraint : a -> Set
    toNat : (x : a) {{_ : ToNatConstraint x}} -> Nat

open ToNat {{...}} public

record FromNeg (a : Set) : Set where
  field
    FromNegConstraint : Nat -> Set
    fromNeg : (n : Nat) {{_ : FromNegConstraint n}} -> a

open FromNeg {{...}} public

{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY FromNeg.fromNeg _ n = fromNeg n #-}

record ToFloat (a : Set) : Set where
  field toFloat : a -> Float

open ToFloat {{...}} public

instance
  FromNat-Nat : FromNat Nat
  FromNat-Nat .FromNatConstraint = const Unit
  FromNat-Nat .fromNat n = n

  ToNat-Nat : ToNat Nat
  ToNat-Nat .ToNatConstraint = const Unit
  ToNat-Nat .toNat n = n

  FromNat-Int : FromNat Int
  FromNat-Int .FromNatConstraint = const Unit
  FromNat-Int .fromNat n = Pos n

  ToNat-Int : ToNat Int
  ToNat-Int .ToNatConstraint i = Assert (isPos i)
  ToNat-Int .toNat (Pos n) = n

  FromNeg-Int : FromNeg Int
  FromNeg-Int .FromNegConstraint = const Unit
  FromNeg-Int .fromNeg n = neg n

  FromNeg-Float : FromNeg Float
  FromNeg-Float .FromNegConstraint = const Unit
  FromNeg-Float .fromNeg x = primFloatNegate (primNatToFloat x)

  ToFloat-Nat : ToFloat Nat
  ToFloat-Nat .toFloat = primNatToFloat

  ToFloat-Int : ToFloat Int
  ToFloat-Int .toFloat (Pos n) = primNatToFloat n
  ToFloat-Int .toFloat (NegSuc n) = primFloatMinus -1.0 (primNatToFloat n)

-------------------------------------------------------------------------------
-- Arithmetic operations
-------------------------------------------------------------------------------

record Addition (a : Set) : Set where
  infixl 6 _+_
  field _+_ : a -> a -> a

open Addition {{...}} public

record Multiplication (a : Set) : Set where
  infixl 7 _*_
  field _*_ : a -> a -> a

open Multiplication {{...}} public

record Power (a : Set) : Set where
  infixr 10 _^_
  field _^_ : a -> Nat -> a

open Power {{...}} public

record Exponentiation (a : Set) : Set where
  infixr 8 _**_
  field _**_ : a -> a -> a

open Exponentiation {{...}} public

record Negation (a : Set) : Set where
  field -_ : a -> a

open Negation {{...}} public

record Subtraction (a : Set) : Set where
  infixl 6 _-_
  field _-_ : a -> a -> a

open Subtraction {{...}} public

record Division (a : Set) : Set where
  infixl 7 _/_
  field
    DivisionConstraint : a -> Set
    _/_ : (x y : a) {{_ : DivisionConstraint y}} -> a

open Division {{...}} public

record Modulus (a : Set) : Set where
  infixl 7 _%_
  field
    ModulusConstraint : a -> Set
    _%_ : (x y : a) {{_ : ModulusConstraint y}} -> a

open Modulus {{...}} public

record Signed (a : Set) : Set where
  field
    abs : a -> a
    signum : a -> a

open Signed {{...}} public

instance
  Addition-Set : Addition Set
  Addition-Set ._+_ = Either

  Multiplication-Set : Multiplication Set
  Multiplication-Set ._*_ = Tuple

  Power-Set : Power Set
  Power-Set ._^_ a = \ where
    0 -> Unit
    1 -> a
    (Suc n) -> a ^ n * a

  Addition-Nat : Addition Nat
  Addition-Nat ._+_ = natPlus

  Multiplication-Nat : Multiplication Nat
  Multiplication-Nat ._*_ = natTimes

  Power-Nat : Power Nat
  Power-Nat ._^_ a = \ where
    0 -> 1
    1 -> a
    (Suc n) -> a ^ n * a

  Exponentiation-Nat : Exponentiation Nat
  Exponentiation-Nat ._**_ = _^_

  Subtraction-Nat : Subtraction Nat
  Subtraction-Nat ._-_ = natMinus

  Division-Nat : Division Nat
  Division-Nat .DivisionConstraint n = Assert (n > 0)
  Division-Nat ._/_ m (Suc n) = natDivAux 0 n m n

  Modulus-Nat : Modulus Nat
  Modulus-Nat .ModulusConstraint n = Assert (n > 0)
  Modulus-Nat ._%_ m (Suc n) = natModAux 0 n m n

  Addition-Int : Addition Int
  Addition-Int ._+_ = add
    where
      sub' : Nat -> Nat -> Int
      sub' m 0 = Pos m
      sub' 0 (Suc n) = NegSuc n
      sub' (Suc m) (Suc n) = sub' m n

      add : Int -> Int -> Int
      add (NegSuc m) (NegSuc n) = NegSuc (Suc (m + n))
      add (NegSuc m) (Pos n) = sub' n (Suc m)
      add (Pos m) (NegSuc n) = sub' m (Suc n)
      add (Pos m) (Pos n) = Pos (m + n)

  Multiplication-Int : Multiplication Int
  Multiplication-Int ._*_ = \ where
    (Pos n) (Pos m) -> Pos (n * m)
    (NegSuc n) (NegSuc m) -> Pos (Suc n * Suc m)
    (Pos n) (NegSuc m) -> neg (n * Suc m)
    (NegSuc n) (Pos m) -> neg (Suc n * m)

  Power-Int : Power Int
  Power-Int ._^_ a = \ where
    0 -> 1
    1 -> a
    (Suc n) -> a ^ n * a

  Negation-Int : Negation Int
  Negation-Int .-_ = \ where
    (Pos 0) -> Pos 0
    (Pos (Suc n)) -> NegSuc n
    (NegSuc n) -> Pos (Suc n)

  Subtraction-Int : Subtraction Int
  Subtraction-Int ._-_ m n = m + (- n)

  Division-Int : Division Int
  Division-Int .DivisionConstraint n = Assert (n > 0)
  Division-Int ._/_ x y with x | y
  ... | Pos m | Pos (Suc n) = Pos (m / Suc n)
  ... | NegSuc m | Pos (Suc n) = neg (Suc m / Suc n)
  ... | Pos m | NegSuc n = neg (m / Suc n)
  ... | NegSuc m | NegSuc n = Pos (Suc m / Suc n)

  Modulus-Int : Modulus Int
  Modulus-Int .ModulusConstraint n = Assert (n > 0)
  Modulus-Int ._%_ x y with x | y
  ... | Pos m | Pos (Suc n) = Pos (m % Suc n)
  ... | NegSuc m | Pos (Suc n) = neg (Suc m % Suc n)
  ... | Pos m | NegSuc n = Pos (m % Suc n)
  ... | NegSuc m | NegSuc n = neg (Suc m % Suc n)

  Signed-Int : Signed Int
  Signed-Int .abs = \ where
    (Pos n) -> Pos n
    (NegSuc n) -> Pos (Suc n)
  Signed-Int .signum = \ where
    (Pos 0) -> Pos 0
    (Pos (Suc _)) -> Pos 1
    (NegSuc _) -> NegSuc 0

  Addition-Float : Addition Float
  Addition-Float ._+_ = primFloatPlus

  Multiplication-Float : Multiplication Float
  Multiplication-Float ._*_ = primFloatTimes

  Power-Float : Power Float
  Power-Float ._^_ a = \ where
    0 -> 1.0
    1 -> a
    (Suc n) -> a ^ n * a

  Exponentiation-Float : Exponentiation Float
  Exponentiation-Float ._**_ x y = exp (y * log x)

  Negation-Float : Negation Float
  Negation-Float .-_ = primFloatNegate

  Subtraction-Float : Subtraction Float
  Subtraction-Float ._-_ = primFloatMinus

  Division-Float : Division Float
  Division-Float .DivisionConstraint = const Unit
  Division-Float ._/_ x y = primFloatDiv x y

  Signed-Float : Signed Float
  Signed-Float .abs x = if x < 0.0 then - x else x
  Signed-Float .signum x with compare x 0.0
  ... | EQ = 0.0
  ... | LT = -1.0
  ... | GT = 1.0

  Addition-Function : {{_ : Addition b}} -> Addition (a -> b)
  Addition-Function ._+_ f g x = f x + g x

  Multiplication-Function : {{_ : Multiplication b}} -> Multiplication (a -> b)
  Multiplication-Function ._*_ f g x = f x * g x

  Negation-Function : {{_ : Negation b}} -> Negation (a -> b)
  Negation-Function .-_ f x = - (f x)

  Subtraction-Function : {{_ : Subtraction b}} -> Subtraction (a -> b)
  Subtraction-Function ._-_ f g x = f x - g x

  Power-Function : Power (a -> a)
  Power-Function ._^_ f = \ where
    0 x -> x
    1 x -> f x
    (Suc n) x -> (f ^ n) (f x)

-------------------------------------------------------------------------------
-- Semigroup
-------------------------------------------------------------------------------

record Semigroup (a : Set) : Set where
  infixr 5 _<>_
  field _<>_ : a -> a -> a

open Semigroup {{...}} public

-- For additive semigroups, monoids, etc.
record Sum (a : Set) : Set where
  constructor Sum:
  field getSum : a

open Sum public

-- For multiplicative semigroups, monoids, etc.
record Product (a : Set) : Set where
  constructor Product:
  field getProduct : a

open Product public

-- For dual semigroups, orders, etc.
record Dual (a : Set) : Set where
  constructor Dual:
  field getDual : a

open Dual public

-- Semigroup where x <> y = x
record First (a : Set) : Set where
  constructor First:
  field getFirst : a

open First public

-- Semigroup where x <> y = y
record Last (a : Set) : Set where
  constructor Last:
  field getLast : a

open Last public

-- For semigroups, monoids, etc. where x <> y = min x y
record Min (a : Set) : Set where
  constructor Min:
  field getMin : a

open Min public

-- For Semigroups, monoids, etc. where x <> y = max x y
record Max (a : Set) : Set where
  constructor Max:
  field getMax : a

open Max public

-- Bool Semigroup where x <> y = x || y.
record Any : Set where
  constructor Any:
  field getAny : Bool

open Any public

-- Bool Semigroup where x <> y = x && y.
record All : Set where
  constructor All:
  field getAll : Bool

open All public

instance
  Semigroup-Dual : {{_ : Semigroup a}} -> Semigroup (Dual a)
  Semigroup-Dual ._<>_ (Dual: x) (Dual: y) = Dual: (y <> x)

  Semigroup-First : Semigroup (First a)
  Semigroup-First ._<>_ x _ = x

  Semigroup-Last : Semigroup (Last a)
  Semigroup-Last ._<>_ _ x = x

  Semigroup-Min : {{_ : Ord a}} -> Semigroup (Min a)
  Semigroup-Min ._<>_ (Min: x) (Min: y) = Min: (min x y)

  Semigroup-Max : {{_ : Ord a}} -> Semigroup (Max a)
  Semigroup-Max ._<>_ (Max: x) (Max: y) = Max: (max x y)

  Semigroup-Any : Semigroup Any
  Semigroup-Any ._<>_ (Any: x) (Any: y) = Any: (x || y)

  Semigroup-All : Semigroup All
  Semigroup-All ._<>_ (All: x) (All: y) = All: (x && y)

  Semigroup-Void : Semigroup Void
  Semigroup-Void ._<>_ = \ ()

  Semigroup-Unit : Semigroup Unit
  Semigroup-Unit ._<>_ unit unit = unit

  Semigroup-Sum-Nat : Semigroup (Sum Nat)
  Semigroup-Sum-Nat ._<>_ (Sum: m) (Sum: n) = Sum: (m + n)

  Semigroup-Product-Nat : Semigroup (Product Nat)
  Semigroup-Product-Nat ._<>_ (Product: x) (Product: y) = Product: (x * y)

  Semigroup-Sum-Int : Semigroup (Sum Int)
  Semigroup-Sum-Int ._<>_ (Sum: m) (Sum: n) = Sum: (m + n)

  Semigroup-Product-Int : Semigroup (Product Int)
  Semigroup-Product-Int ._<>_ (Product: x) (Product: y) = Product: (x * y)

  Semigroup-String : Semigroup String
  Semigroup-String ._<>_ = primStringAppend

  Semigroup-Function : {{_ : Semigroup b}} -> Semigroup (a -> b)
  Semigroup-Function ._<>_ f g = \ x -> f x <> g x

  Semigroup-Either : {{_ : Semigroup a}} {{_ : Semigroup b}}
    -> Semigroup (Either a b)
  Semigroup-Either ._<>_ (Left _) x = x
  Semigroup-Either ._<>_ x _ = x

  Semigroup-Tuple : {{_ : Semigroup a}} {{_ : Semigroup b}}
    -> Semigroup (Tuple a b)
  Semigroup-Tuple ._<>_ (x , y) (w , z) = (x <> w , y <> z)

  Semigroup-Maybe : {{_ : Semigroup a}} -> Semigroup (Maybe a)
  Semigroup-Maybe ._<>_ = \ where
    Nothing x -> x
    x Nothing -> x
    (Just x) (Just y) -> Just (x <> y)

  Semigroup-List : Semigroup (List a)
  Semigroup-List ._<>_ xs ys = listrec ys (\ z _ zs -> z :: zs) xs

  Semigroup-IO : {{_ : Semigroup a}} -> Semigroup (IO a)
  Semigroup-IO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

  Semigroup-Identity : {{_ : Semigroup a}} -> Semigroup (Identity a)
  Semigroup-Identity ._<>_ (Identity: x) (Identity: y) =
    Identity: (x <> y)

  Semigroup-Const : {{_ : Semigroup a}} -> Semigroup (Const a b)
  Semigroup-Const ._<>_ (Const: x) (Const: y) = Const: (x <> y)

  Semigroup-Endo : Semigroup (Endo a)
  Semigroup-Endo ._<>_ g f = Endo: \ x -> appEndo g (appEndo f x)

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Set) : Set where
  field
    overlap {{Semigroup-super}} : Semigroup a
    mempty : a

open Monoid {{...}} public

instance
  Monoid-Dual : {{_ : Monoid a}} -> Monoid (Dual a)
  Monoid-Dual .mempty = Dual: mempty

  Monoid-First : {{_ : Monoid a}} -> Monoid (First a)
  Monoid-First .mempty = First: mempty

  Monoid-Last : {{_ : Monoid a}} -> Monoid (Last a)
  Monoid-Last .mempty = Last: mempty

  Monoid-Unit : Monoid Unit
  Monoid-Unit .mempty = unit

  Monoid-All : Monoid All
  Monoid-All .mempty = All: True

  Monoid-Any : Monoid Any
  Monoid-Any .mempty = Any: False

  Monoid-SumNat : Monoid (Sum Nat)
  Monoid-SumNat .mempty = Sum: 0

  Monoid-ProductNat : Monoid (Product Nat)
  Monoid-ProductNat .mempty = Product: 1

  Monoid-SumInt : Monoid (Sum Int)
  Monoid-SumInt .mempty = Sum: 0

  Monoid-ProductInt : Monoid (Product Int)
  Monoid-ProductInt .mempty = Product: 1

  Monoid-String : Monoid String
  Monoid-String .mempty = ""

  Monoid-Function : {{_ : Monoid b}} -> Monoid (a -> b)
  Monoid-Function .mempty = const mempty

  Monoid-Endo : Monoid (Endo a)
  Monoid-Endo .mempty = Endo: \ x -> x

  Monoid-Maybe : {{_ : Semigroup a}} -> Monoid (Maybe a)
  Monoid-Maybe .mempty = Nothing

  Monoid-List : Monoid (List a)
  Monoid-List .mempty = []

  Monoid-IO : {{_ : Monoid a}} -> Monoid (IO a)
  Monoid-IO .mempty = pureIO mempty

  Monoid-Identity : {{_ : Monoid a}} -> Monoid (Identity a)
  Monoid-Identity .mempty = Identity: mempty

  Monoid-Const : {{_ : Monoid a}} -> Monoid (Const a b)
  Monoid-Const .mempty = Const: mempty

-------------------------------------------------------------------------------
-- Nonempty
-------------------------------------------------------------------------------

record NonemptyConstraint (a : Set) : Set where
  field Nonempty : a -> Set

open NonemptyConstraint {{...}} public

instance
  NonemptyConstraint-Maybe : NonemptyConstraint (Maybe a)
  NonemptyConstraint-Maybe .Nonempty Nothing = Void
  NonemptyConstraint-Maybe .Nonempty _ = Unit

  NonemptyConstraint-List : NonemptyConstraint (List a)
  NonemptyConstraint-List .Nonempty [] = Void
  NonemptyConstraint-List .Nonempty _ = Unit

  NonemptyConstraint-String : NonemptyConstraint String
  NonemptyConstraint-String .Nonempty "" = Void
  NonemptyConstraint-String .Nonempty _ = Unit

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

record Category (hom : Set -> Set -> Set) : Set where
  infixr 9 _<<<_
  field
    id : hom a a
    _<<<_ : hom b c -> hom a b -> hom a c

  infixr 9 _>>>_
  _>>>_ : hom a b -> hom b c -> hom a c
  _>>>_ = flip _<<<_

open Category {{...}} public

instance
  Category-Function : Category Function
  Category-Function .id x = x
  Category-Function ._<<<_ g f x = g (f x)

-------------------------------------------------------------------------------
-- Functor, Contravariant, Bifunctor, Profunctor
-------------------------------------------------------------------------------

record Functor (f : Set -> Set) : Set where
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

  flap : f (a -> b) -> a -> f b
  flap f x = map (_$ x) f

  void : f a -> f Unit
  void = map (const unit)

open Functor {{...}} public

record Contravariant (f : Set -> Set) : Set where
  field contramap : (a -> b) -> f b -> f a

  phantom : {{_ : Functor f}} -> f a -> f b
  phantom x = contramap (const unit) (map (const unit) x)

open Contravariant {{...}} public

record Bifunctor (p : Set -> Set -> Set) : Set where
  field bimap : (a -> b) -> (c -> d) -> p a c -> p b d

  first : (a -> b) -> p a c -> p b c
  first f = bimap f id

  second : (b -> c) -> p a b -> p a c
  second g = bimap id g

open Bifunctor {{...}} public

record Profunctor (p : Set -> Set -> Set) : Set where
  field dimap : (a -> b) -> (c -> d) -> p b c -> p a d

  lmap : (a -> b) -> p b c -> p a c
  lmap f = dimap f id

  rmap : (b -> c) -> p a b -> p a c
  rmap f = dimap id f

open Profunctor {{...}} public

instance
  Profunctor-Function : Profunctor Function
  Profunctor-Function .dimap f g h = g <<< h <<< f

  Functor-Function : Functor (Function a)
  Functor-Function .map = rmap

  Bifunctor-Either : Bifunctor Either
  Bifunctor-Either .bimap f g = either (Left <<< f) (Right <<< g)

  Functor-Either : Functor (Either a)
  Functor-Either .map = second

  Bifunctor-Tuple : Bifunctor Tuple
  Bifunctor-Tuple .bimap f g = tuple (f <<< fst) (g <<< snd)

  Functor-Tuple : Functor (Tuple a)
  Functor-Tuple .map = second

  Functor-Maybe : Functor Maybe
  Functor-Maybe .map f = \ where
    Nothing -> Nothing
    (Just a) -> Just (f a)

  Functor-List : Functor List
  Functor-List .map f = listrec [] \ a _ bs -> f a :: bs

  Functor-IO : Functor IO
  Functor-IO .map = mapIO

  Functor-Identity : Functor Identity
  Functor-Identity .map f = Identity: <<< f <<< runIdentity

  Bifunctor-Const : Bifunctor Const
  Bifunctor-Const .bimap f g = Const: <<< f <<< getConst

  Functor-Const : Functor (Const a)
  Functor-Const .map = second

  Contravariant-Const : Contravariant (Const a)
  Contravariant-Const .contramap f = Const: <<< getConst

  Functor-Sum : Functor Sum
  Functor-Sum .map f = Sum: <<< f <<< getSum

  Functor-Product : Functor Product
  Functor-Product .map f = Product: <<< f <<< getProduct

  Functor-Dual : Functor Dual
  Functor-Dual .map f = Dual: <<< f <<< getDual

  Functor-First : Functor First
  Functor-First .map f = First: <<< f <<< getFirst

  Functor-Last : Functor Last
  Functor-Last .map f = Last: <<< f <<< getLast

  Functor-Min : Functor Min
  Functor-Min .map f = Min: <<< f <<< getMin

  Functor-Max : Functor Max
  Functor-Max .map f = Max: <<< f <<< getMax

-------------------------------------------------------------------------------
-- Applicative
-------------------------------------------------------------------------------

record Applicative (f : Set -> Set) : Set where
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

  liftA : (a -> b) -> f a -> f b
  liftA f x = (| f x |)

  replicateA : Nat -> f a -> f (List a)
  replicateA {a} n0 fa = loop n0
    where
      loop : Nat -> f (List a)
      loop 0 = pure []
      loop (Suc n) = (| _::_ fa (loop n) |)

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
forever : {{_ : Applicative f}} -> f a -> f b
forever as = as *> forever as

instance
  Applicative-Function : Applicative (Function a)
  Applicative-Function .pure = const
  Applicative-Function ._<*>_ f x = \ a -> f a (x a)

  Applicative-Either : Applicative (Either a)
  Applicative-Either .pure = Right
  Applicative-Either ._<*>_ = \ where
    (Left a) _ -> Left a
    (Right f) -> map f

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

  Applicative-Identity : Applicative Identity
  Applicative-Identity .pure = Identity:
  Applicative-Identity ._<*>_ = map <<< runIdentity

  Applicative-Const : {{_ : Monoid a}} -> Applicative (Const a)
  Applicative-Const .pure _ = Const: mempty
  Applicative-Const ._<*>_ (Const: f) (Const: a) = Const: (f <> a)

  Applicative-Sum : Applicative Sum
  Applicative-Sum .pure = Sum:
  Applicative-Sum ._<*>_ (Sum: f) (Sum: x) = Sum: (f x)

  Applicative-Product : Applicative Product
  Applicative-Product .pure = Product:
  Applicative-Product ._<*>_ (Product: f) (Product: x) = Product: (f x)

  Applicative-Dual : Applicative Dual
  Applicative-Dual .pure = Dual:
  Applicative-Dual ._<*>_ (Dual: f) (Dual: x) = Dual: (f x)

  Applicative-First : Applicative First
  Applicative-First .pure = First:
  Applicative-First ._<*>_ (First: f) (First: x) = First: (f x)

  Applicative-Last : Applicative Last
  Applicative-Last .pure = Last:
  Applicative-Last ._<*>_ (Last: f) (Last: x) = Last: (f x)

  Applicative-Min : Applicative Min
  Applicative-Min .pure = Min:
  Applicative-Min ._<*>_ (Min: f) (Min: x) = Min: (f x)

  Applicative-Max : Applicative Max
  Applicative-Max .pure = Max:
  Applicative-Max ._<*>_ (Max: f) (Max: x) = Max: (f x)

-------------------------------------------------------------------------------
-- Alternative
-------------------------------------------------------------------------------

record Alternative (f : Set -> Set) : Set where
  infixl 3 _<|>_
  field
    overlap {{Alternative-super}} : Applicative f
    _<|>_ : f a -> f a -> f a
    empty : f a

  guard : Bool -> f Unit
  guard True = pure unit
  guard False = empty

open Alternative {{...}} public

instance
  Alternative-Maybe : Alternative Maybe
  Alternative-Maybe .empty = Nothing
  Alternative-Maybe ._<|>_ = \ where
    Nothing r -> r
    l _ -> l

  Alternative-List : Alternative List
  Alternative-List .empty = mempty
  Alternative-List ._<|>_ = _<>_

--------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

record Monad (m : Set -> Set) : Set where
  infixl 1 _>>=_
  field
    overlap {{Applicative-super}} : Applicative m
    _>>=_ : m a -> (a -> m b) -> m b

  join : m (m a) -> m a
  join = _>>= id

  infixr 1 _=<<_
  _=<<_ : (a -> m b) -> m a -> m b
  _=<<_ = flip _>>=_

  infixl 4 _>>_
  _>>_ : m a -> m b -> m b
  _>>_ = _*>_

  infixl 4 _<<_
  _<<_ : m b -> m a -> m b
  _<<_ = _<*_

  infixr 1 _>=>_
  _>=>_ : (a -> m b) -> (b -> m c) -> a -> m c
  (f >=> g) x = f x >>= g

  infixr 1 _<=<_
  _<=<_ : (b -> m c) -> (a -> m b) -> a -> m c
  _<=<_ = flip _>=>_

  liftM : (a -> b) -> m a -> m b
  liftM f x = x >>= pure <<< f

  ap : m (a -> b) -> m a -> m b
  ap f x = do
    g <- f
    y <- x
    pure (g y)

open Monad {{...}} public

return : forall {a m} {{_ : Monad m}} -> a -> m a
return = pure

instance
  Monad-Function : Monad (Function a)
  Monad-Function ._>>=_ m k = \ a -> k (m a) a

  Monad-Either : Monad (Either a)
  Monad-Either ._>>=_ = \ where
    (Left a) _ -> Left a
    (Right x) k -> k x

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

  Monad-Identity : Monad Identity
  Monad-Identity ._>>=_ (Identity: x) k = k x

  Monad-Sum : Monad Sum
  Monad-Sum ._>>=_ (Sum: x) k = k x

  Monad-Product : Monad Product
  Monad-Product ._>>=_ (Product: x) k = k x

  Monad-Dual : Monad Dual
  Monad-Dual ._>>=_ (Dual: x) k = k x

  Monad-First : Monad First
  Monad-First ._>>=_ (First: x) k = k x

  Monad-Last : Monad Last
  Monad-Last ._>>=_ (Last: x) k = k x

  Monad-Min : Monad Min
  Monad-Min ._>>=_ (Min: x) k = k x

  Monad-Max : Monad Max
  Monad-Max ._>>=_ (Max: x) k = k x

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

record Enum (a : Set) : Set where
  field enumFromTo : a -> a -> List a

open Enum {{...}} public

instance
  Enum-Int : Enum Int
  Enum-Int .enumFromTo m n =
      let k = toNat (abs (m - n)) {{believeMe}}
      in go k m n
    where
      go : Nat -> Int -> Int -> List Int
      go 0 m _ = [ m ]
      go (Suc k) m n =
        let m' = if m < n then m + 1 else (m - 1)
        in m :: go k m' n

  Enum-Nat : Enum Nat
  Enum-Nat .enumFromTo m n = map
    (\ k -> toNat k {{believeMe}})
    (enumFromTo (Pos m) (Pos n))

  Enum-Char : Enum Char
  Enum-Char .enumFromTo c d = chr <$> enumFromTo (ord c) (ord d)

-------------------------------------------------------------------------------
-- Show
-------------------------------------------------------------------------------

ShowS : Set
ShowS = String -> String

record Show (a : Set) : Set where
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

private
  primitive
    primShowNat : Nat -> String
    primShowInteger : Int -> String
    primShowFloat : Float -> String
    primShowChar : Char -> String
    primShowString : String -> String

instance
  Show-Void : Show Void
  Show-Void .showsPrec _ ()

  Show-Unit : Show Unit
  Show-Unit .showsPrec _ unit = showString "unit"

  Show-Bool : Show Bool
  Show-Bool .showsPrec _ True = showString "True"
  Show-Bool .showsPrec _ False = showString "False"

  Show-Nat : Show Nat
  Show-Nat .showsPrec _ = showString <<< primShowNat

  Show-Int : Show Int
  Show-Int .showsPrec _ = showString <<< primShowInteger

  Show-Float : Show Float
  Show-Float .showsPrec _ = showString <<< primShowFloat

  Show-Char : Show Char
  Show-Char .showsPrec _ = showString <<< primShowChar

  Show-String : Show String
  Show-String .showsPrec _ = showString <<< primShowString

  Show-Tuple : {{_ : Show a}} {{_ : Show b}} -> Show (Tuple a b)
  Show-Tuple .showsPrec d (x , y) = showString "(" <<< showsPrec d x
    <<< showString " , " <<< showsPrec d y <<< showString ")"

  Show-Either : {{_ : Show a}} {{_ : Show b}} -> Show (Either a b)
  Show-Either .showsPrec d (Left x) = showParen (d > appPrec)
    (showString "Left " <<< showsPrec appPrec+1 x)
  Show-Either .showsPrec d (Right x) = showParen (d > appPrec)
    (showString "Right " <<< showsPrec appPrec+1 x)

  Show-Maybe : {{_ : Show a}} -> Show (Maybe a)
  Show-Maybe .showsPrec d (Just x) = showParen (d > appPrec)
    (showString "Just " <<< showsPrec appPrec+1 x)
  Show-Maybe .showsPrec d Nothing = showString "Nothing"

  Show-List : {{_ : Show a}} -> Show (List a)
  Show-List .showsPrec _ [] = showString "[]"
  Show-List .showsPrec d (x :: xs) = showString "[" <<< content <<< showString "]"
    where
      content : ShowS
      content = showsPrec d x <<< go xs
        where
          go : {{_ : Show a}} -> List a -> ShowS
          go [] = showString ""
          go (y :: ys) = showString ", " <<< showsPrec d y <<< go ys

  Show-Identity : {{_ : Show a}} -> Show (Identity a)
  Show-Identity .showsPrec d (Identity: x) = showParen (d > appPrec)
    (showString "Identity: " <<< showsPrec appPrec+1 x)

  Show-Const : {{_ : Show a}} -> Show (Const a b)
  Show-Const .showsPrec d (Const: x) = showParen (d > appPrec)
    (showString "Const: " <<< showsPrec appPrec+1 x)

  Show-Sum : {{_ : Show a}} -> Show (Sum a)
  Show-Sum .showsPrec d (Sum: x) = showParen (d > appPrec)
    (showString "Show: " <<< showsPrec appPrec+1 x)

  Show-Product : {{_ : Show a}} -> Show (Product a)
  Show-Product .showsPrec d (Product: x) = showParen (d > appPrec)
    (showString "Product: " <<< showsPrec appPrec+1 x)

  Show-Dual : {{_ : Show a}} -> Show (Dual a)
  Show-Dual .showsPrec d (Dual: x) = showParen (d > appPrec)
    (showString "Dual: " <<< showsPrec appPrec+1 x)

  Show-First : {{_ : Show a}} -> Show (First a)
  Show-First .showsPrec d (First: x) = showParen (d > appPrec)
    (showString "First: " <<< showsPrec appPrec+1 x)

  Show-Last : {{_ : Show a}} -> Show (Last a)
  Show-Last .showsPrec d (Last: x) = showParen (d > appPrec)
    (showString "Last: " <<< showsPrec appPrec+1 x)

  Show-Min : {{_ : Show a}} -> Show (Min a)
  Show-Min .showsPrec d (Min: x) = showParen (d > appPrec)
    (showString "Min: " <<< showsPrec appPrec+1 x)

  Show-Max : {{_ : Show a}} -> Show (Max a)
  Show-Max .showsPrec d (Max: x) = showParen (d > appPrec)
    (showString "Max: " <<< showsPrec appPrec+1 x)

  Show-Any : Show Any
  Show-Any .showsPrec d (Any: x) = showParen (d > appPrec)
    (showString "Any: " <<< showsPrec appPrec+1 x)

  Show-All : Show All
  Show-All .showsPrec d (All: x) = showParen (d > appPrec)
    (showString "All: " <<< showsPrec appPrec+1 x)

-------------------------------------------------------------------------------
-- Console IO
-------------------------------------------------------------------------------

postulate
  putStr : String -> IO Unit
  putStrLn : String -> IO Unit
  getLine : IO String
  getContents : IO String

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStrLn (f s)

print : {{_ : Show a}} -> a -> IO Unit
print x = putStrLn (show x)

{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC putStr = T.putStr #-}
{-# COMPILE GHC putStrLn = T.putStrLn #-}
{-# COMPILE GHC getLine = T.getLine #-}
{-# COMPILE GHC getContents = T.getContents #-}

-------------------------------------------------------------------------------
-- Size
-------------------------------------------------------------------------------

{-# BUILTIN SIZEUNIV SizeU #-}
{-# BUILTIN SIZE Size #-}
{-# BUILTIN SIZELT Size<_ #-}
{-# BUILTIN SIZESUC SizeSuc #-}
{-# BUILTIN SIZEINF Inf #-}
{-# BUILTIN SIZEMAX SizeMax #-}

{-# FOREIGN GHC
  type SizeLT i = ()
#-}

{-# COMPILE GHC Size = type () #-}
{-# COMPILE GHC Size<_ = type SizeLT #-}
{-# COMPILE GHC SizeSuc = \_ -> () #-}
{-# COMPILE GHC Inf = () #-}
{-# COMPILE GHC SizeMax = \_ _ -> () #-}

-------------------------------------------------------------------------------
-- Thunk
-------------------------------------------------------------------------------

record Thunk (i : Size) (f : Size -> Set) : Set where
  coinductive
  field force : {j : Size< i} -> f j

open Thunk public
