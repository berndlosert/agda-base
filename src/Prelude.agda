{-# OPTIONS --type-in-type #-}

module Prelude where

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c d r s : Set
    f m : Set -> Set
    p : Set -> Set -> Set

-------------------------------------------------------------------------------
-- Primitive types
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

data Ordering : Set where
  LT EQ GT : Ordering

data Nat : Set where
  Zero : Nat
  Suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data Fin : Nat -> Set where
  Zero : {n : Nat} -> Fin (Suc n)
  Suc : {n : Nat} -> Fin n -> Fin (Suc n)

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

record Thunk (i : Size) (f : Size -> Set) : Set where
  coinductive
  field force : {j : Size< i} -> f j

open Thunk public

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
-- Void primitives
-------------------------------------------------------------------------------

absurd : Void -> a
absurd ()

-------------------------------------------------------------------------------
-- Bool primitives
-------------------------------------------------------------------------------

Assert : Bool -> Set
Assert False = Void
Assert True = Unit

bool : Bool -> a -> a -> a
bool False x _ = x
bool True _ x = x

infixr 0 if_then_else_
if_then_else_ : Bool -> a -> a -> a
if b then x else y = bool b y x

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
  natModAux k m (Suc n) Zero = natModAux Zero m n m
  natModAux k m (Suc n) (Suc j) = natModAux (Suc k) m n j

  natDiv : Nat -> Nat -> Nat
  natDiv m (Suc n) = natDivAux Zero n m n
  natDiv _ _ = undefined

  natMod : Nat -> Nat -> Nat
  natMod m (Suc n) = natModAux Zero n m n
  natMod _ _ = undefined

{-# BUILTIN NATEQUALS natEquality #-}
{-# BUILTIN NATLESS natLessThan #-}
{-# BUILTIN NATPLUS natPlus #-}
{-# BUILTIN NATMINUS natMinus #-}
{-# BUILTIN NATTIMES natTimes #-}
{-# BUILTIN NATDIVSUCAUX natDivAux #-}
{-# BUILTIN NATMODSUCAUX natModAux #-}

neg : Nat -> Int
neg 0 = Pos 0
neg (Suc n) = NegSuc n

-------------------------------------------------------------------------------
-- Fin primitives
-------------------------------------------------------------------------------

private
  finToNat : {n : Nat} -> Fin n -> Nat
  finToNat Zero = Zero
  finToNat (Suc n) = Suc (finToNat n)

  natToFin : (m n : Nat) -> Maybe (Fin n)
  natToFin Zero (Suc j) = Just Zero
  natToFin (Suc m) (Suc n) with natToFin m n
  ... | Just k' = Just (Suc k')
  ... | Nothing = Nothing
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
  finPlus {n} k m with natToFin (natMod (natPlus (finToNat k) (finToNat m)) n) n
  ... | Just k' = k'
  ... | Nothing = undefined

  finNegate : {n : Nat} -> Fin n -> Fin n
  finNegate {n} m with natToFin (natMinus n (finToNat m)) n
  ... | Just k = k
  ... | Nothing = undefined

  finMinus : {n : Nat} -> Fin n -> Fin n -> Fin n
  finMinus k m = finPlus k (finNegate m)

  finTimes : {n : Nat} -> Fin n -> Fin n -> Fin n
  finTimes {n} k m
    with natToFin (natMod (natTimes (finToNat k) (finToNat m)) n) n
  ... | Just k' = k'
  ... | Nothing = undefined

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
    (Pos n) (NegSuc m) -> neg (natTimes n (Suc m))
    (NegSuc n) (Pos m) -> neg (natTimes (Suc n) m)

  intDiv : Int -> Int -> Int
  intDiv = \ where
    (Pos m) (Pos n) -> Pos (natDiv m n)
    (Pos m) (NegSuc n) -> neg (natDiv m (Suc n))
    (NegSuc m) (Pos n) -> neg (natDiv (Suc m) n)
    (NegSuc m) (NegSuc n) -> Pos (natDiv (Suc m) (Suc n))

  intMod : Int -> Int -> Int
  intMod = \ where
    (Pos m) (Pos n) -> Pos (natMod m n)
    (Pos m) (NegSuc n) -> Pos (natMod m (Suc n))
    (NegSuc m) (Pos n) -> neg (natMod (Suc m) n)
    (NegSuc m) (NegSuc n) -> neg (natMod (Suc m) (Suc n))

-------------------------------------------------------------------------------
-- Float primitives
-------------------------------------------------------------------------------

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

NaN : Float
NaN = primFloatDiv 0.0 0.0

Infinity -Infinity : Float
Infinity = primFloatDiv 1.0 0.0
-Infinity = primFloatNegate Infinity

-------------------------------------------------------------------------------
-- Char primitives
-------------------------------------------------------------------------------

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

minChar maxChar : Char
minChar = '\NUL'
maxChar = '\1114111'

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
chr : Fin (Suc (ord maxChar)) -> Char
chr n = primNatToChar (finToNat n)

-------------------------------------------------------------------------------
-- String primitives
-------------------------------------------------------------------------------

private
  primitive
    primStringEquality : String -> String -> Bool
    primStringToList : String -> List Char
    primStringFromList : List Char -> String
    primStringAppend : String -> String -> String

pack = primStringFromList
unpack = primStringToList

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

fromLeft : (x : Either a b) {{_ : Assert $ isLeft x}} -> a
fromLeft (Left a) = a

fromRight : (x : Either a b) {{_ : Assert $ isRight x}} -> b
fromRight (Right b) = b

-------------------------------------------------------------------------------
-- Tuple primitives
-------------------------------------------------------------------------------

tuple : (a -> b) -> (a -> c) -> a -> Tuple b c
tuple f g x = (f x , g x)

swap : Tuple a b -> Tuple b a
swap = tuple snd fst

dup : a -> Tuple a a
dup x = (x , x)

uncurry : (a -> b -> c) -> Tuple a b -> c
uncurry f (x , y) = f x y

curry : (Tuple a b -> c) -> a -> b -> c
curry f x y = f (x , y)

apply : Tuple (a -> b) a -> b
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

fromJust : (x : Maybe a) {{_ : Assert $ isJust x}} -> a
fromJust (Just a) = a

maybe : b -> (a -> b) -> Maybe a -> b
maybe b f Nothing = b
maybe b f (Just a) = f a

-------------------------------------------------------------------------------
-- List primitives
-------------------------------------------------------------------------------

pattern [_] x = x :: []

list : b -> (a -> List a -> b) -> List a -> b
list b f [] = b
list b f (a :: as) = f a as

listrec : b -> (a -> List a -> b -> b) -> List a -> b
listrec b f [] = b
listrec b f (a :: as) = f a as (listrec b f as)

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

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

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
  Ord-Float ._<_ = primFloatNumericalLess

  Ord-Char : Ord Char
  Ord-Char ._<_ x y = ord x < ord y

  Ord-List : {{_ : Ord a}} -> Ord (List a)
  Ord-List ._<_ = \ where
    (x :: xs) (y :: ys) -> x < y || (x == y && xs < ys)
    _ _ -> False

  Ord-String : Ord String
  Ord-String ._<_ l r = unpack l < unpack r

  Ord-Tuple : {{_ : Ord a}} {{_ : Ord b}} -> Ord (Tuple a b)
  Ord-Tuple ._<_ (x , y) (w , z) = x < w || (x == w && y < z)

  Ord-Maybe : {{_ : Ord a}} -> Ord (Maybe a)
  Ord-Maybe ._<_ = \ where
    _ Nothing -> False
    Nothing _ -> True
    (Just x) (Just y) -> x < y

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

  FromNat-Set : FromNat Set
  FromNat-Set .FromNatConstraint _ = Unit
  FromNat-Set .fromNat 0 = Void
  FromNat-Set .fromNat 1 = Unit
  FromNat-Set .fromNat (Suc n) = Either (fromNat 1) (fromNat n)

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
  FromNeg-Int .fromNeg n = neg n

  ToFloat-Nat : ToFloat Nat
  ToFloat-Nat .toFloat = primNatToFloat

  ToFloat-Int : ToFloat Int
  ToFloat-Int .toFloat (Pos n) = primNatToFloat n
  ToFloat-Int .toFloat (NegSuc n) = primFloatMinus -1.0 (primNatToFloat n)

-------------------------------------------------------------------------------
-- Additive
-------------------------------------------------------------------------------

record Additive (a : Set) : Set where
  infixl 6 _+_
  field
    _+_ : a -> a -> a
    zero : a

open Additive {{...}} public

instance
  Additive-Set : Additive Set
  Additive-Set ._+_ = Either
  Additive-Set .zero = Void

  Additive-Nat : Additive Nat
  Additive-Nat ._+_ = natPlus
  Additive-Nat .zero = 0

  Additive-Fin : {n : Nat} -> Additive (Fin (Suc n))
  Additive-Fin ._+_ = finPlus
  Additive-Fin .zero = Zero

  Additive-Int : Additive Int
  Additive-Int .zero = 1
  Additive-Int ._+_ = intPlus

  Additive-Float : Additive Float
  Additive-Float ._+_ = primFloatPlus
  Additive-Float .zero = 0.0

  Additive-Function : {{_ : Additive b}} -> Additive (a -> b)
  Additive-Function ._+_ f g x = f x + g x
  Additive-Function .zero = const zero

-------------------------------------------------------------------------------
-- Substractable
-------------------------------------------------------------------------------

record Subtractable (a : Set) : Set where
  infixl 6 _-_
  field _-_ : a -> a -> a

open Subtractable {{...}} public

instance
  Subtractable-Nat : Subtractable Nat
  Subtractable-Nat ._-_ = natMinus

  Subtractable-Fin : {n : Nat} -> Subtractable (Fin (Suc n))
  Subtractable-Fin ._-_ = finMinus

  Subtractable-Int : Subtractable Int
  Subtractable-Int ._-_ m n = m + intNegate n

  Subtractable-Float : Subtractable Float
  Subtractable-Float ._-_ = primFloatMinus

  Subtractable-Function : {{_ : Subtractable b}} -> Subtractable (a -> b)
  Subtractable-Function ._-_ f g x = f x - g x

-------------------------------------------------------------------------------
-- Negatable
-------------------------------------------------------------------------------

record Negatable (a : Set) : Set where
  field -_ : a -> a

open Negatable {{...}} public

instance
  Negatable-Fin : {n : Nat} -> Negatable (Fin (Suc n))
  Negatable-Fin .-_ = finNegate

  Negatable-Int : Negatable Int
  Negatable-Int .-_ = intNegate

  Negatable-Float : Negatable Float
  Negatable-Float .-_ = primFloatNegate

  Negatable-Function : {{_ : Negatable b}} -> Negatable (a -> b)
  Negatable-Function .-_ f x = - (f x)

-------------------------------------------------------------------------------
-- Multiplicative
-------------------------------------------------------------------------------

record Multiplicative (a : Set) : Set where
  infixl 7 _*_
  field
    _*_ : a -> a -> a
    one : a

  infixr 8 _^_
  _^_ : a -> Nat -> a
  a ^ 0 = one
  a ^ (Suc n) = a ^ n * a

open Multiplicative {{...}} public

instance
  Multiplicative-Set : Multiplicative Set
  Multiplicative-Set ._*_ = Tuple
  Multiplicative-Set .one = Unit

  Multiplicative-Nat : Multiplicative Nat
  Multiplicative-Nat ._*_ = natTimes
  Multiplicative-Nat .one = 1

  Multiplicative-Fin : {n : Nat} -> Multiplicative (Fin (Suc (Suc n)))
  Multiplicative-Fin .one = Suc Zero
  Multiplicative-Fin ._*_ = finTimes

  Multiplicative-Int : Multiplicative Int
  Multiplicative-Int .one = 1
  Multiplicative-Int ._*_ = intTimes

  Multiplicative-Float : Multiplicative Float
  Multiplicative-Float ._*_ = primFloatTimes
  Multiplicative-Float .one = 1.0

  Multiplicative-Function : {{_ : Multiplicative b}} -> Multiplicative (a -> b)
  Multiplicative-Function ._*_ f g x = f x * g x
  Multiplicative-Function .one = const one

-------------------------------------------------------------------------------
-- Dividable
-------------------------------------------------------------------------------

record Dividable (a : Set) : Set where
  infixl 7 _/_
  infixl 7 _%_
  field
    DividableConstraint : a -> Set
    _/_ _%_ : (x y : a) {{_ : DividableConstraint y}} -> a

open Dividable {{...}} public

instance
  Dividable-Nat : Dividable Nat
  Dividable-Nat .DividableConstraint n = Assert (n /= 0)
  Dividable-Nat ._/_ m n = natDiv m n
  Dividable-Nat ._%_ m n = natMod m n

  Dividable-Int : Dividable Int
  Dividable-Int .DividableConstraint n = Assert (n /= 0)
  Dividable-Int ._/_ m n = intDiv m n
  Dividable-Int ._%_ m n = intMod m n

  Dividable-Float : Dividable Float
  Dividable-Float .DividableConstraint _ = Unit
  Dividable-Float ._/_ x y = primFloatDiv x y
  Dividable-Float ._%_ _ _ = 0.0

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

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Set) : Set where
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

  Monoid-Function : {{_ : Monoid b}} -> Monoid (a -> b)
  Monoid-Function .neutral = const neutral

  Monoid-Tuple : {{_ : Monoid a}} {{_ : Monoid b}} -> Monoid (Tuple a b)
  Monoid-Tuple .neutral = (neutral , neutral)

  Monoid-Maybe : {{_ : Semigroup a}} -> Monoid (Maybe a)
  Monoid-Maybe .neutral = Nothing

  Monoid-List : Monoid (List a)
  Monoid-List .neutral = []

  Monoid-IO : {{_ : Monoid a}} -> Monoid (IO a)
  Monoid-IO .neutral = pureIO neutral

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

record Category (p : Set -> Set -> Set) : Set where
  field
    compose : p b c -> p a b -> p a c
    identity : p a a

  infixr 9 _<<<_
  _<<<_ : p b c -> p a b -> p a c
  _<<<_ = compose

  infixr 9 _>>>_
  _>>>_ : p a b -> p b c -> p a c
  _>>>_ = flip compose

open Category {{...}} public

id : forall {a} {p} {{_ : Category p}} -> p a a
id = identity

instance
  Category-Function : Category Function
  Category-Function .compose f g x = f (g x)
  Category-Function .identity x = x

-------------------------------------------------------------------------------
-- Functor
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

  void : f a -> f Unit
  void = unit <$_

  vacuous : f Void -> f a
  vacuous = map absurd

open Functor {{...}} public

instance
  Functor-Function : Functor (Function a)
  Functor-Function .map = _<<<_

  Functor-Either : Functor (Either a)
  Functor-Either .map f = either Left (Right <<< f)

  Functor-Tuple : Functor (Tuple a)
  Functor-Tuple .map f (x , y) = (x , f y)

  Functor-Maybe : Functor Maybe
  Functor-Maybe .map f = maybe Nothing (Just <<< f)

  Functor-List : Functor List
  Functor-List .map f = listrec [] \ a _ bs -> f a :: bs

  Functor-IO : Functor IO
  Functor-IO .map = mapIO

-------------------------------------------------------------------------------
-- Contravariant
-------------------------------------------------------------------------------

record Contravariant (f : Set -> Set) : Set where
  field cmap : (a -> b) -> f b -> f a

  phantom : {{_ : Functor f}} -> f a -> f b
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

  Bifunctor-Tuple : Bifunctor Tuple
  Bifunctor-Tuple .lmap f (x , y) = (f x , y)

-------------------------------------------------------------------------------
-- Profunctor
-------------------------------------------------------------------------------

record Profunctor (p : Set -> Set -> Set) : Set where
  field
    overlap {{Functor-super}} : Functor (p a)
    lcmap : (b -> a) -> p a c -> p b c

  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lcmap f <<< map g

  arr : {{_ : Category p}} -> (a -> b) -> p a b
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

  infixl 4 _*>_
  _*>_ : f a -> f b -> f b
  a *> b = (| (flip const) a b |)

  infixl 4 _<*_
  _<*_ : f a -> f b -> f a
  a <* b = (| const a b |)

  liftA : (a -> b) -> f a -> f b
  liftA f x = (| f x |)

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
  Applicative-Function ._<*>_ f g = \ x -> f x (g x)

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

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

record Enum (a : Set) : Set where
  field
    {{Ord-super}} : Ord a
    SucConstraint : a -> Set
    PredConstraint : a -> Set
    suc : (x : a) {{_ : SucConstraint x}} -> a
    pred : (x : a) {{_ : PredConstraint x}} -> a
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
      go 0 m _ = [ m ]
      go (Suc k) m n =
        let m' = if m < n then m + 1 else m - 1
        in m :: go k m' n

  Enum-Int : Enum Int
  Enum-Int .SucConstraint _ = Unit
  Enum-Int .PredConstraint _ = Unit
  Enum-Int .suc n = n + 1
  Enum-Int .pred n = n - 1
  Enum-Int .enumFromTo m n with m - n
  ... | Pos k = (\ i -> Pos i + n) <$> enumFromTo k 0
  ... | NegSuc k = (\ i -> Pos i + m) <$> enumFromTo 0 (Suc k)

  Enum-Char : Enum Char
  Enum-Char .SucConstraint c = Assert (c < maxChar)
  Enum-Char .PredConstraint c = Assert (c > minChar)
  Enum-Char .suc c = primNatToChar $ suc (ord c)
  Enum-Char .pred c = primNatToChar $ pred (ord c) {{trustMe}}
  Enum-Char .enumFromTo c d = primNatToChar <$> enumFromTo (ord c) (ord d)

-------------------------------------------------------------------------------
-- Bounded
-------------------------------------------------------------------------------

record Bounded (a : Set) : Set where
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
  Show-Bool .showsPrec _ b = showString (if b then "True" else "False")

  Show-Ordering : Show Ordering
  Show-Ordering .showsPrec _ = \ where
    LT -> showString "LT"
    EQ -> showString "EQ"
    GT -> showString "GT"

  Show-Nat : Show Nat
  Show-Nat .showsPrec _ = showString <<< primShowNat

  Show-Fin : {n : Nat} -> Show (Fin n)
  Show-Fin .showsPrec _ = showString <<< primShowNat <<< finToNat

  Show-Int : Show Int
  Show-Int .showsPrec _ = showString <<< primShowInteger

  Show-Float : Show Float
  Show-Float .showsPrec _ = showString <<< primShowFloat

  Show-Char : Show Char
  Show-Char .showsPrec _ = showString <<< primShowChar

  Show-String : Show String
  Show-String .showsPrec _ = showString <<< primShowString

  Show-Function : Show (Function a b)
  Show-Function .showsPrec _ _ = showString "<function>"

  Show-Tuple : {{_ : Show a}} {{_ : Show b}} -> Show (Tuple a b)
  Show-Tuple .showsPrec d (x , y) = showString "(" <<< showsPrec d x
    <<< showString " , " <<< showsPrec d y <<< showString ")"

  Show-Either : {{_ : Show a}} {{_ : Show b}} -> Show (Either a b)
  Show-Either .showsPrec d = \ where
    (Left x) -> showParen (d > appPrec)
      (showString "Left " <<< showsPrec appPrec+1 x)
    (Right x) -> showParen (d > appPrec)
      (showString "Right " <<< showsPrec appPrec+1 x)

  Show-Maybe : {{_ : Show a}} -> Show (Maybe a)
  Show-Maybe .showsPrec d = \ where
    (Just x) -> showParen (d > appPrec)
      (showString "Just " <<< showsPrec appPrec+1 x)
    Nothing -> showString "Nothing"

  Show-List : {{_ : Show a}} -> Show (List a)
  Show-List .showsPrec _ [] = showString "[]"
  Show-List .showsPrec d (x :: xs) =
      showString "[" <<< content <<< showString "]"
    where
      content : ShowS
      content = showsPrec d x <<< go xs
        where
          go : {{_ : Show a}} -> List a -> ShowS
          go [] = showString ""
          go (y :: ys) = showString ", " <<< showsPrec d y <<< go ys
