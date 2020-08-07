module Prelude where

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

record Endo a : Set where
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

id : a -> a
id x = x

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

infixr 9 _∘_
_∘_ : (b -> c) -> (a -> b) -> a -> c
g ∘ f = λ x -> g (f x)

Assert : Bool -> Set
Assert False = Void
Assert True = Unit

infixr 10 if_then_else_
if_then_else_ : Bool -> a -> a -> a
if True then x else _ = x
if False then _ else x = x

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

foldZ : (Nat -> a) -> (Nat -> a) -> Int -> a
foldZ f g (Pos n) = f n
foldZ f g (NegSuc n) = g n

isPos : Int -> Bool
isPos (Pos _) = True
isPos _ = False

fromPos : (i : Int) {{_ : Assert $ isPos i}} -> Nat
fromPos (Pos n) = n

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

natToFloat = primNatToFloat
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

intToFloat : Int -> Float
intToFloat (Pos n) = natToFloat n
intToFloat (NegSuc n) = primFloatMinus -1.0 (natToFloat n)

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

unpack = primStringToList
pack = primStringFromList

either : (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left a) = f a
either f g (Right b) = g b

mirror : Either a b -> Either b a
mirror = either Right Left

untag : Either a a -> a
untag (Left a) = a
untag (Right a) = a

isLeft : Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight : Either a b -> Bool
isRight (Left _) = False
isRight _ = True

fromLeft : a -> Either a b -> a
fromLeft _ (Left x) = x
fromLeft x (Right _) = x

fromRight : b -> Either a b -> b
fromRight x (Left _) = x
fromRight _ (Right x) = x

fromEither : (a -> b) -> Either a b -> b
fromEither f (Left x) = f x
fromEither _ (Right x) = x

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
apply = uncurry _$_

isJust : Maybe a -> Bool
isJust (Just _) = True
isJust _ = False

isNothing : Maybe a -> Bool
isNothing (Just _) = False
isNothing _ = True

fromJust : (m : Maybe a) {{_ : Assert $ isJust m}} -> a
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

-------------------------------------------------------------------------------
-- Boolean
-------------------------------------------------------------------------------

record Boolean (b : Set) : Set where
  infixr 2 _||_
  infixr 3 _&&_
  field
    ff : b
    tt : b
    not : b -> b
    _||_ : b -> b -> b
    _&&_ : b -> b -> b

open Boolean {{...}} public

instance
  BooleanBool : Boolean Bool
  BooleanBool .ff = False
  BooleanBool .tt = True
  BooleanBool .not = λ where
    False -> True
    True -> False
  BooleanBool ._||_ = λ where
    False b -> b
    True _ -> True
  BooleanBool ._&&_ = λ where
    False _ -> False
    True b -> b

  BooleanFunction : {{_ : Boolean b}} -> Boolean (a -> b)
  BooleanFunction .ff x = ff
  BooleanFunction .tt x = tt
  BooleanFunction .not f x = not (f x)
  BooleanFunction ._||_ f g x = f x || g x
  BooleanFunction ._&&_ f g x = f x && g x

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
  EqVoid : Eq Void
  EqVoid ._==_ = λ ()

  EqUnit : Eq Unit
  EqUnit ._==_ unit unit = True

  EqBool : Eq Bool
  EqBool ._==_ = λ where
    True True -> True
    False False -> False
    _ _ -> False

  EqNat : Eq Nat
  EqNat ._==_ = natEquality

  EqInt : Eq Int
  EqInt ._==_ = λ where
    (Pos m) (Pos n) -> m == n
    (NegSuc m) (NegSuc n) -> m == n
    _ _ -> False

  EqFloat : Eq Float
  EqFloat ._==_ = primFloatNumericalEquality

  EqChar : Eq Char
  EqChar ._==_ = primCharEquality

  EqString : Eq String
  EqString ._==_ = primStringEquality

  EqEither : {{_ : Eq a}} {{_ : Eq b}} -> Eq (Either a b)
  EqEither ._==_ = λ where
    (Left x) (Left y) -> x == y
    (Right x) (Right y) -> x == y
    _ _ -> False

  EqTuple : {{_ : Eq a}} {{_ : Eq b}} -> Eq (Tuple a b)
  EqTuple ._==_ (x , y) (w , z) = (x == w) && (y == z)

  EqMaybe : {{_ : Eq a}} -> Eq (Maybe a)
  EqMaybe ._==_ = λ where
    Nothing Nothing -> True
    (Just x) (Just y) -> x == y
    _ _ -> False

  EqList : {{_ : Eq a}} -> Eq (List a)
  EqList ._==_ = λ where
    [] [] -> True
    (x :: xs) (y :: ys) -> x == y && xs == ys
    _ _ -> False

  EqIdentity : {{_ : Eq a}} -> Eq (Identity a)
  EqIdentity ._==_ (Identity: x) (Identity: y) = x == y

  EqConst : {{_ : Eq a}} -> Eq (Const a b)
  EqConst ._==_ (Const: x) (Const: y) = x == y

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (a : Set) : Set where
  infixl 4 _<_
  field
    overlap {{super}} : Eq a
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
  OrdVoid : Ord Void
  OrdVoid ._<_ = λ ()

  OrdUnit : Ord Unit
  OrdUnit ._<_ unit unit = False

  OrdBool : Ord Bool
  OrdBool ._<_ = λ where
    False True -> True
    _ _ -> False

  OrdNat : Ord Nat
  OrdNat ._<_ = natLessThan

  OrdInt : Ord Int
  OrdInt ._<_ = λ where
    (Pos m) (Pos n) -> m < n
    (NegSuc m) (NegSuc n) -> m > n
    (NegSuc _) (Pos _) -> True
    (Pos _) (NegSuc _) -> False

  OrdFloat : Ord Float
  OrdFloat ._<_ = primFloatNumericalLess

  OrdChar : Ord Char
  OrdChar ._<_ x y = ord x < ord y

  OrdList : {{_ : Ord a}} -> Ord (List a)
  OrdList ._<_ = λ where
    (x :: xs) (y :: ys) -> x < y || (x == y && xs < ys)
    [] [] -> True
    _ _ -> False

  OrdString : Ord String
  OrdString ._<_ l r with unpack l | unpack r
  ... | (x :: xs) | (y :: ys) = x < y || (x == y && xs < ys)
  ... | _ | _ = False

  OrdTuple : {{_ : Ord a}} {{_ : Ord b}} -> Ord (Tuple a b)
  OrdTuple ._<_ (x , y) (w , z) = x < w || (x == w && y < z)

  OrdMaybe : {{_ : Ord a}} -> Ord (Maybe a)
  OrdMaybe ._<_ = λ where
    _ Nothing -> False
    Nothing _ -> True
    (Just x) (Just y) -> x < y

  OrdIdentity : {{_ : Ord a}} -> Ord (Identity a)
  OrdIdentity ._<_ (Identity: x) (Identity: y) = x < y

  OrdConst : {{_ : Ord a}} -> Ord (Const a b)
  OrdConst ._<_ (Const: x) (Const: y) = x < y

-------------------------------------------------------------------------------
-- FromNat and FromNeg
-------------------------------------------------------------------------------

record FromNat (a : Set) : Set where
  field
    Constraint : Nat -> Set
    fromNat : (n : Nat) {{_ : Constraint n}} -> a

open FromNat {{...}} public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY FromNat.fromNat _ n = fromNat n #-}

record FromNeg (a : Set) : Set where
  field
    Constraint : Nat -> Set
    fromNeg : (n : Nat) {{_ : Constraint n}} -> a

open FromNeg {{...}} public using (fromNeg)

{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY FromNeg.fromNeg _ n = fromNeg n #-}

instance
  FromNatNat : FromNat Nat
  FromNatNat = record {
      Constraint = const Unit;
      fromNat = λ n -> n
    }

  FromNatInt : FromNat Int
  FromNatInt = record {
      Constraint = const Unit;
      fromNat = λ n -> Pos n
    }

  FromNegInt : FromNeg Int
  FromNegInt = record {
      Constraint = const Unit;
      fromNeg = λ n -> neg n
    }

  FromNegFloat : FromNeg Float
  FromNegFloat = record {
      Constraint = const Unit;
      fromNeg = λ x -> primFloatNegate (natToFloat x)
    }

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
  AdditionSet : Addition Set
  AdditionSet ._+_ = Either

  MultiplicationSet : Multiplication Set
  MultiplicationSet ._*_ = Tuple

  PowerSet : Power Set
  PowerSet ._^_ a = λ where
    0 -> Unit
    1 -> a
    (Suc n) -> a ^ n * a

  AdditionNat : Addition Nat
  AdditionNat ._+_ = natPlus

  MultiplicationNat : Multiplication Nat
  MultiplicationNat ._*_ = natTimes

  PowerNat : Power Nat
  PowerNat ._^_ a = λ where
    0 -> 1
    1 -> a
    (Suc n) -> a ^ n * a

  ExponentiationNat : Exponentiation Nat
  ExponentiationNat ._**_ = _^_

  SubtractionNat : Subtraction Nat
  SubtractionNat ._-_ = natMinus

  DivisionNat : Division Nat
  DivisionNat .DivisionConstraint n = Assert (n > 0)
  DivisionNat ._/_ m (Suc n) = natDivAux 0 n m n

  ModulusNat : Modulus Nat
  ModulusNat .ModulusConstraint n = Assert (n > 0)
  ModulusNat ._%_ m (Suc n) = natModAux 0 n m n

  AdditionInt : Addition Int
  AdditionInt ._+_ = add
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

  MultiplicationInt : Multiplication Int
  MultiplicationInt ._*_ = λ where
    (Pos n) (Pos m) -> Pos (n * m)
    (NegSuc n) (NegSuc m) -> Pos (Suc n * Suc m)
    (Pos n) (NegSuc m) -> neg (n * Suc m)
    (NegSuc n) (Pos m) -> neg (Suc n * m)

  PowerInt : Power Int
  PowerInt ._^_ a = λ where
    0 -> 1
    1 -> a
    (Suc n) -> a ^ n * a

  NegationInt : Negation Int
  NegationInt .-_ = λ where
    (Pos 0) -> Pos 0
    (Pos (Suc n)) -> NegSuc n
    (NegSuc n) -> Pos (Suc n)

  SubtractionInt : Subtraction Int
  SubtractionInt ._-_ m n = m + (- n)

  DivisionInt : Division Int
  DivisionInt .DivisionConstraint n = Assert (n > 0)
  DivisionInt ._/_ x y with x | y
  ... | Pos m | Pos (Suc n) = Pos (m / Suc n)
  ... | NegSuc m | Pos (Suc n) = neg (Suc m / Suc n)
  ... | Pos m | NegSuc n = neg (m / Suc n)
  ... | NegSuc m | NegSuc n = Pos (Suc m / Suc n)

  ModulusInt : Modulus Int
  ModulusInt .ModulusConstraint n = Assert (n > 0)
  ModulusInt ._%_ x y with x | y
  ... | Pos m | Pos (Suc n) = Pos (m % Suc n)
  ... | NegSuc m | Pos (Suc n) = neg (Suc m % Suc n)
  ... | Pos m | NegSuc n = Pos (m % Suc n)
  ... | NegSuc m | NegSuc n = neg (Suc m % Suc n)

  SignedInt : Signed Int
  SignedInt .abs = λ where
    (Pos n) -> Pos n
    (NegSuc n) -> Pos (Suc n)
  SignedInt .signum = λ where
    (Pos 0) -> Pos 0
    (Pos (Suc _)) -> Pos 1
    (NegSuc _) -> NegSuc 0

  AdditionFloat : Addition Float
  AdditionFloat ._+_ = primFloatPlus

  MultiplicationFloat : Multiplication Float
  MultiplicationFloat ._*_ = primFloatTimes

  PowerFloat : Power Float
  PowerFloat ._^_ a = λ where
    0 -> 1.0
    1 -> a
    (Suc n) -> a ^ n * a

  ExponentiationFloat : Exponentiation Float
  ExponentiationFloat ._**_ x y = exp (y * log x)

  NegationFloat : Negation Float
  NegationFloat .-_ = primFloatNegate

  SubtractionFloat : Subtraction Float
  SubtractionFloat ._-_ = primFloatMinus

  DivisionFloat : Division Float
  DivisionFloat .DivisionConstraint = const Unit
  DivisionFloat ._/_ x y = primFloatDiv x y

  SignedFloat : Signed Float
  SignedFloat .abs x = if x < 0.0 then - x else x
  SignedFloat .signum x with compare x 0.0
  ... | EQ = 0.0
  ... | LT = -1.0
  ... | GT = 1.0

  AdditionFunction : {{_ : Addition b}} -> Addition (a -> b)
  AdditionFunction ._+_ f g x = f x + g x

  MultiplicationFunction : {{_ : Multiplication b}} -> Multiplication (a -> b)
  MultiplicationFunction ._*_ f g x = f x * g x

  NegationFunction : {{_ : Negation b}} -> Negation (a -> b)
  NegationFunction .-_ f x = - (f x)

  SubtractionFunction : {{_ : Subtraction b}} -> Subtraction (a -> b)
  SubtractionFunction ._-_ f g x = f x - g x

  PowerFunction : Power (a -> a)
  PowerFunction ._^_ f = λ where
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
  SemigroupDual : {{_ : Semigroup a}} -> Semigroup (Dual a)
  SemigroupDual ._<>_ (Dual: x) (Dual: y) = Dual: (y <> x)

  SemigroupFirst : Semigroup (First a)
  SemigroupFirst ._<>_ x _ = x

  SemigroupLast : Semigroup (Last a)
  SemigroupLast ._<>_ _ x = x

  SemigroupMin : {{_ : Ord a}} -> Semigroup (Min a)
  SemigroupMin ._<>_ (Min: x) (Min: y) = Min: (min x y)

  SemigroupMax : {{_ : Ord a}} -> Semigroup (Max a)
  SemigroupMax ._<>_ (Max: x) (Max: y) = Max: (max x y)

  SemigroupAny : Semigroup Any
  SemigroupAny ._<>_ (Any: x) (Any: y) = Any: (x || y)

  SemigroupAll : Semigroup All
  SemigroupAll ._<>_ (All: x) (All: y) = All: (x && y)

  SemigroupVoid : Semigroup Void
  SemigroupVoid ._<>_ = λ ()

  SemigroupUnit : Semigroup Unit
  SemigroupUnit ._<>_ unit unit = unit

  SemigroupSumNat : Semigroup (Sum Nat)
  SemigroupSumNat ._<>_ (Sum: m) (Sum: n) = Sum: (m + n)

  SemigroupProductNat : Semigroup (Product Nat)
  SemigroupProductNat ._<>_ (Product: x) (Product: y) = Product: (x * y)

  SemigroupSumInt : Semigroup (Sum Int)
  SemigroupSumInt ._<>_ (Sum: m) (Sum: n) = Sum: (m + n)

  SemigroupProductInt : Semigroup (Product Int)
  SemigroupProductInt ._<>_ (Product: x) (Product: y) = Product: (x * y)

  SemigroupString : Semigroup String
  SemigroupString ._<>_ = primStringAppend

  SemigroupFunction : {{_ : Semigroup b}} -> Semigroup (a -> b)
  SemigroupFunction ._<>_ f g = λ x -> f x <> g x

  SemigroupEither : {{_ : Semigroup a}} {{_ : Semigroup b}}
    -> Semigroup (Either a b)
  SemigroupEither ._<>_ (Left _) x = x
  SemigroupEither ._<>_ x _ = x

  SemigroupTuple : {{_ : Semigroup a}} {{_ : Semigroup b}}
    -> Semigroup (Tuple a b)
  SemigroupTuple ._<>_ (x , y) (w , z) = (x <> w , y <> z)

  SemigroupMaybe : {{_ : Semigroup a}} -> Semigroup (Maybe a)
  SemigroupMaybe ._<>_ = λ where
    Nothing x -> x
    x Nothing -> x
    (Just x) (Just y) -> Just (x <> y)

  SemigroupList : Semigroup (List a)
  SemigroupList ._<>_ xs ys = listrec ys (λ z _ zs -> z :: zs) xs

  SemigroupIdentity : {{_ : Semigroup a}} -> Semigroup (Identity a)
  SemigroupIdentity ._<>_ (Identity: x) (Identity: y) =
    Identity: (x <> y)

  SemigroupConst : {{_ : Semigroup a}} -> Semigroup (Const a b)
  SemigroupConst ._<>_ (Const: x) (Const: y) = Const: (x <> y)

  SemigroupEndo : Semigroup (Endo a)
  SemigroupEndo ._<>_ g f = Endo: λ x -> appEndo g (appEndo f x)

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Set) : Set where
  field
    overlap {{super}} : Semigroup a
    neutral : a

  when : Bool -> a -> a
  when True a = a
  when False _ = neutral

  unless : Bool -> a -> a
  unless True _ = neutral
  unless False a = a

open Monoid {{...}} public

instance
  MonoidDual : {{_ : Monoid a}} -> Monoid (Dual a)
  MonoidDual .neutral = Dual: neutral

  MonoidFirst : {{_ : Monoid a}} -> Monoid (First a)
  MonoidFirst .neutral = First: neutral

  MonoidLast : {{_ : Monoid a}} -> Monoid (Last a)
  MonoidLast .neutral = Last: neutral

  MonoidUnit : Monoid Unit
  MonoidUnit .neutral = unit

  MonoidAll : Monoid All
  MonoidAll .neutral = All: True

  MonoidAny : Monoid Any
  MonoidAny .neutral = Any: False

  MonoidSumNat : Monoid (Sum Nat)
  MonoidSumNat .neutral = Sum: 0

  MonoidProductNat : Monoid (Product Nat)
  MonoidProductNat .neutral = Product: (Suc 0)

  MonoidSumInt : Monoid (Sum Int)
  MonoidSumInt .neutral = Sum: 0

  MonoidProductInt : Monoid (Product Int)
  MonoidProductInt .neutral = Product: 1

  MonoidString : Monoid String
  MonoidString .neutral = ""

  MonoidFunction : {{_ : Monoid b}} -> Monoid (a -> b)
  MonoidFunction .neutral = const neutral

  MonoidEndo : Monoid (Endo a)
  MonoidEndo .neutral = Endo: λ x -> x

  MonoidMaybe : {{_ : Semigroup a}} -> Monoid (Maybe a)
  MonoidMaybe .neutral = Nothing

  MonoidList : Monoid (List a)
  MonoidList .neutral = []

  MonoidIdentity : {{_ : Monoid a}} -> Monoid (Identity a)
  MonoidIdentity .neutral = Identity: neutral

  MonoidConst : {{_ : Monoid a}} -> Monoid (Const a b)
  MonoidConst .neutral = Const: neutral

-------------------------------------------------------------------------------
-- IsBuildable, Buildable
-------------------------------------------------------------------------------

record IsBuildable (s a : Set) : Set where
  field
    {{monoid}} : Monoid s
    singleton : a -> s

  infixr 5 _++_
  _++_ : s -> s -> s
  _++_ = _<>_

  nil : s
  nil = neutral

  cons : a -> s -> s
  cons a s = singleton a ++ s

  snoc : s -> a -> s
  snoc s a = s ++ singleton a

  fromList : List a -> s
  fromList [] = nil
  fromList (a :: as) = cons a (fromList as)

  fromMaybe : Maybe a -> s
  fromMaybe Nothing = nil
  fromMaybe (Just a) = singleton a

  replicate : Nat -> a -> s
  replicate n a = applyN (cons a) n nil

open IsBuildable {{...}} public

Buildable : (Set -> Set) -> Set
Buildable f = forall {a} -> IsBuildable (f a) a

instance
  BuildableList : Buildable List
  BuildableList .singleton = _:: []

  IsBuildableStringChar : IsBuildable String Char
  IsBuildableStringChar .singleton c = pack (singleton c)

-------------------------------------------------------------------------------
-- Functor, Contravariant, Bifunctor, Profunctor
-------------------------------------------------------------------------------

infixr 0 _~>_
_~>_ : (f g : Set -> Set) -> Set
f ~> g  = forall {a} -> f a -> g a

record Functor (f : Set -> Set) : Set where
  field map : (a -> b) -> f a -> f b

  infixl 4 _<$>_
  _<$>_ : (a -> b) -> f a -> f b
  _<$>_ = map

  infixl 4 _<$_
  _<$_ : b -> f a -> f b
  _<$_ = map ∘ const

  infixl 4 _$>_
  _$>_ : f a -> b -> f b
  _$>_ = flip _<$_

  void : f a -> f Unit
  void = map (const unit)

open Functor {{...}} public

record Contravariant (f : Set -> Set) : Set where
  field contramap : (a -> b) -> f b -> f a

  phantom : {{_ : Functor f}} -> f a -> f b
  phantom x = contramap (const unit) $ map (const unit) x

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
  ProfunctorFunction : Profunctor Function
  ProfunctorFunction .dimap f g h = g ∘ h ∘ f

  FunctorFunction : Functor (Function a)
  FunctorFunction .map = rmap

  BifunctorEither : Bifunctor Either
  BifunctorEither .bimap f g = either (Left ∘ f) (Right ∘ g)

  FunctorEither : Functor (Either a)
  FunctorEither .map = second

  BifunctorTuple : Bifunctor Tuple
  BifunctorTuple .bimap f g = tuple (f ∘ fst) (g ∘ snd)

  FunctorTuple : Functor (Tuple a)
  FunctorTuple .map = second

  FunctorMaybe : Functor Maybe
  FunctorMaybe .map f = λ where
    Nothing -> Nothing
    (Just a) -> Just (f a)

  FunctorList : Functor List
  FunctorList .map f = listrec [] λ a _ bs -> f a :: bs

  FunctorIdentity : Functor Identity
  FunctorIdentity .map f = Identity: ∘ f ∘ runIdentity

  BifunctorConst : Bifunctor Const
  BifunctorConst .bimap f g = Const: ∘ f ∘ getConst

  FunctorConst : Functor (Const a)
  FunctorConst .map = second

  ContravariantConst : Contravariant (Const a)
  ContravariantConst .contramap f = Const: ∘ getConst

  FunctorSum : Functor Sum
  FunctorSum .map f = Sum: ∘ f ∘ getSum

  FunctorProduct : Functor Product
  FunctorProduct .map f = Product: ∘ f ∘ getProduct

  FunctorDual : Functor Dual
  FunctorDual .map f = Dual: ∘ f ∘ getDual

  FunctorFirst : Functor First
  FunctorFirst .map f = First: ∘ f ∘ getFirst

  FunctorLast : Functor Last
  FunctorLast .map f = Last: ∘ f ∘ getLast

  FunctorMin : Functor Min
  FunctorMin .map f = Min: ∘ f ∘ getMin

  FunctorMax : Functor Max
  FunctorMax .map f = Max: ∘ f ∘ getMax

-------------------------------------------------------------------------------
-- Applicative
-------------------------------------------------------------------------------

record Applicative (f : Set -> Set) : Set where
  infixl 4 _<*>_
  field
    overlap {{super}} : Functor f
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

  replicateA : {{_ : IsBuildable s a}} -> Nat -> f a -> f s
  replicateA {s} {a} n0 fa = loop n0
    where
      loop : Nat -> f s
      loop 0 = pure nil
      loop (Suc n) = (| cons fa (loop n) |)

  replicateA! : Nat -> f a -> f Unit
  replicateA! n0 fa = loop n0
    where
      loop : Nat -> f Unit
      loop 0 = pure unit
      loop (Suc n) = fa *> loop n

open Applicative {{...}} public

forever : {{_ : Applicative f}} -> f a -> f b
forever as = as *> forever as

instance
  ApplicativeFunction : Applicative (Function a)
  ApplicativeFunction .pure = const
  ApplicativeFunction ._<*>_ f x = λ a -> f a (x a)

  ApplicativeEither : Applicative (Either a)
  ApplicativeEither .pure = Right
  ApplicativeEither ._<*>_ = λ where
    (Left a) _ -> Left a
    (Right f) -> map f

  ApplicativeMaybe : Applicative Maybe
  ApplicativeMaybe .pure = Just
  ApplicativeMaybe ._<*>_ = λ where
    (Just f) -> map f
    Nothing _ -> Nothing

  ApplicativeList : Applicative List
  ApplicativeList .pure = singleton
  ApplicativeList ._<*>_ = λ where
    [] _ -> []
    _ [] -> []
    (f :: fs) (x :: xs) -> f x :: (fs <*> xs)

  ApplicativeIdentity : Applicative Identity
  ApplicativeIdentity .pure = Identity:
  ApplicativeIdentity ._<*>_ = map ∘ runIdentity

  ApplicativeConst : {{_ : Monoid a}} -> Applicative (Const a)
  ApplicativeConst .pure _ = Const: neutral
  ApplicativeConst ._<*>_ (Const: f) (Const: a) = Const: (f <> a)

  ApplicativeSum : Applicative Sum
  ApplicativeSum .pure = Sum:
  ApplicativeSum ._<*>_ (Sum: f) (Sum: x) = Sum: (f x)

  ApplicativeProduct : Applicative Product
  ApplicativeProduct .pure = Product:
  ApplicativeProduct ._<*>_ (Product: f) (Product: x) = Product: (f x)

  ApplicativeDual : Applicative Dual
  ApplicativeDual .pure = Dual:
  ApplicativeDual ._<*>_ (Dual: f) (Dual: x) = Dual: (f x)

  ApplicativeFirst : Applicative First
  ApplicativeFirst .pure = First:
  ApplicativeFirst ._<*>_ (First: f) (First: x) = First: (f x)

  ApplicativeLast : Applicative Last
  ApplicativeLast .pure = Last:
  ApplicativeLast ._<*>_ (Last: f) (Last: x) = Last: (f x)

  ApplicativeMin : Applicative Min
  ApplicativeMin .pure = Min:
  ApplicativeMin ._<*>_ (Min: f) (Min: x) = Min: (f x)

  ApplicativeMax : Applicative Max
  ApplicativeMax .pure = Max:
  ApplicativeMax ._<*>_ (Max: f) (Max: x) = Max: (f x)

-------------------------------------------------------------------------------
-- Alternative
-------------------------------------------------------------------------------

record Alternative (f : Set -> Set) : Set where
  infixl 3 _<|>_
  field
    overlap {{super}} : Applicative f
    _<|>_ : f a -> f a -> f a
    empty : f a

  guard : Bool -> f Unit
  guard True = pure unit
  guard False = empty

open Alternative {{...}} public

instance
  AlternativeMaybe : Alternative Maybe
  AlternativeMaybe .empty = Nothing
  AlternativeMaybe ._<|>_ = λ where
    Nothing r -> r
    l _ -> l

  AlternativeList : Alternative List
  AlternativeList .empty = neutral
  AlternativeList ._<|>_ = _<>_

-------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

record Monad (m : Set -> Set) : Set where
  infixl 1 _>>=_
  field
    overlap {{super}} : Applicative m
    _>>=_ : m a -> (a -> m b) -> m b

  join : m (m a) -> m a
  join = _>>= id

  infixl 1 _>>_
  _>>_ : m a -> m b -> m b
  _>>_ = _*>_

  liftM : (a -> b) -> m a -> m b
  liftM f x = x >>= pure ∘ f

  ap : m (a -> b) -> m a -> m b
  ap f x = do
    g <- f
    y <- x
    pure (g y)

open Monad {{...}} public

return : forall {a m} {{_ : Monad m}} -> a -> m a
return = pure

instance
  MonadFunction : Monad (Function a)
  MonadFunction ._>>=_ m k = λ a -> k (m a) a

  MonadEither : Monad (Either a)
  MonadEither ._>>=_ = λ where
    (Left a) _ -> Left a
    (Right x) k -> k x

  MonadMaybe : Monad Maybe
  MonadMaybe ._>>=_ = λ where
    Nothing _ -> Nothing
    (Just x) k -> k x

  MonadList : Monad List
  MonadList ._>>=_ = λ where
    [] k -> []
    (x :: xs) k -> k x ++ (xs >>= k)

  MonadIdentity : Monad Identity
  MonadIdentity ._>>=_ (Identity: x) k = k x

  MonadSum : Monad Sum
  MonadSum ._>>=_ (Sum: x) k = k x

  MonadProduct : Monad Product
  MonadProduct ._>>=_ (Product: x) k = k x

  MonadDual : Monad Dual
  MonadDual ._>>=_ (Dual: x) k = k x

  MonadFirst : Monad First
  MonadFirst ._>>=_ (First: x) k = k x

  MonadLast : Monad Last
  MonadLast ._>>=_ (Last: x) k = k x

  MonadMin : Monad Min
  MonadMin ._>>=_ (Min: x) k = k x

  MonadMax : Monad Max
  MonadMax ._>>=_ (Max: x) k = k x

-------------------------------------------------------------------------------
-- IsFoldable, Foldable
-------------------------------------------------------------------------------

record IsFoldable (s a : Set) : Set where
  field foldMap : {{_ : Monoid b}} -> (a -> b) -> s -> b

  fold : {{_ : Monoid a}} -> s -> a
  fold = foldMap id

  foldr : (a -> b -> b) -> b -> s -> b
  foldr f b as = appEndo (foldMap (Endo: ∘ f) as) b

  foldl : (b -> a -> b) -> b -> s -> b
  foldl f b as =
    (appEndo ∘ getDual) (foldMap (Dual: ∘ Endo: ∘ flip f) as) b

  foldrM : {{_ : Monad m}} -> (a -> b -> m b) -> b -> s -> m b
  foldrM f b as = let g k a b' = f a b' >>= k in
    foldl g return as b

  foldlM : {{_ : Monad m}} -> (b -> a -> m b) -> b -> s -> m b
  foldlM f b as = let g a k b' = f b' a >>= k in
    foldr g return as b

  toList : s -> List a
  toList = foldMap [_]

  count : s -> Nat
  count = getSum ∘ foldMap (const $ Sum: (Suc 0))

  all : (a -> Bool) -> s -> Bool
  all p = getAll ∘ foldMap (All: ∘ p)

  any : (a -> Bool) -> s -> Bool
  any p = getAny ∘ foldMap (Any: ∘ p)

  null : s -> Bool
  null = foldr (λ _ _ -> False) True

  sum : {{ _ : Monoid (Sum a)}} -> s -> a
  sum = getSum ∘ foldMap Sum:

  product : {{ _ : Monoid (Product a)}} -> s -> a
  product = getProduct ∘ foldMap Product:

  find : (a -> Bool) -> s -> Maybe a
  find p = leftToMaybe ∘
    foldlM (λ _ a ->  if p a then Left a else Right unit) unit

  module _ {{_ : Eq a}} where

    elem : a -> s -> Bool
    elem = any ∘ _==_

    notElem : a -> s -> Bool
    notElem a s = not (elem a s)

  module _ {{_ : Applicative f}} where

    traverse! : (a -> f b) -> s -> f Unit
    traverse! f = foldr (_*>_ ∘ f) (pure unit)

    for! : s -> (a -> f b) -> f Unit
    for! = flip traverse!

  module _ {{_ : Boolean a}} where

    or : s -> a
    or = foldr _||_ ff

    and : s -> a
    and = foldr _&&_ tt

open IsFoldable {{...}} public

sequence! : {{_ : Applicative f}} {{_ : IsFoldable s (f a)}} -> s -> f Unit
sequence! = traverse! id

asum : {{_ : Alternative f}} {{_ : IsFoldable s (f a)}} -> s -> f a
asum = foldr _<|>_ empty

Foldable : (Set -> Set) -> Set
Foldable f = forall {a} -> IsFoldable (f a) a

instance
  IsFoldableNatUnit : IsFoldable Nat Unit
  IsFoldableNatUnit .foldMap b 0 = neutral
  IsFoldableNatUnit .foldMap b (Suc n) = b unit <> foldMap b n

  FoldableMaybe : Foldable Maybe
  FoldableMaybe .foldMap = maybe neutral

  FoldableList : Foldable List
  FoldableList .foldMap f = listrec neutral λ x _ y -> f x <> y

  IsFoldableStringChar : IsFoldable String Char
  IsFoldableStringChar .foldMap f = foldMap f ∘ unpack

-------------------------------------------------------------------------------
-- IsFoldable1, Foldable1
-------------------------------------------------------------------------------

record IsFoldable1 (s a : Set) : Set where
  field
    {{super}} : IsFoldable s a
    Nonempty : s -> Set

  foldMap1 : {{_ : Semigroup b}}
    -> (a -> b) -> (xs : s) {{_ : Nonempty xs}} -> b
  foldMap1 f s = fromJust (foldMap (Just ∘ f) s) {{believeMe}}

  fold1 : {{_ : Semigroup a}} (xs : s) {{_ : Nonempty xs}} -> a
  fold1 s = fromJust (foldMap Just s) {{believeMe}}

  foldr1 : (a -> a -> a) -> (xs : s) {{_ : Nonempty xs}} -> a
  foldr1 f s = fromJust (foldr g Nothing s) {{believeMe}}
    where
      g : a -> Maybe a -> Maybe a
      g x Nothing = Just x
      g x (Just y) = Just (f x y)

  foldl1 : (a -> a -> a) -> (xs : s) {{_ : Nonempty xs}} -> a
  foldl1 f s = fromJust (foldl g Nothing s) {{believeMe}}
    where
      g : Maybe a -> a -> Maybe a
      g Nothing x = Just x
      g (Just x) y = Just (f x y)

  module _ {{_ : Ord a}} where

    minimum : (xs : s) {{_ : Nonempty xs}} -> a
    minimum = foldr1 min

    maximum : (xs : s) {{_ : Nonempty xs}} -> a
    maximum = foldr1 max

open IsFoldable1 {{...}} public

Foldable1 : (Set -> Set) -> Set
Foldable1 f = forall {a} -> IsFoldable1 (f a) a

instance
  IsFoldable1NatUnit : IsFoldable1 Nat Unit
  IsFoldable1NatUnit .Nonempty 0 = Void
  IsFoldable1NatUnit .Nonempty _ = Unit

  Foldable1Maybe : Foldable1 Maybe
  Foldable1Maybe .Nonempty Nothing = Void
  Foldable1Maybe .Nonempty _ = Unit

  Foldable1List : Foldable1 List
  Foldable1List .Nonempty [] = Void
  Foldable1List .Nonempty _ = Unit

  IsFoldable1StringChar : IsFoldable1 String Char
  IsFoldable1StringChar .Nonempty "" = Void
  IsFoldable1StringChar .Nonempty _ = Unit

-------------------------------------------------------------------------------
-- Traversable
-------------------------------------------------------------------------------

private
  record StateL (s a : Set) : Set where
    constructor stateL:
    field runStateL : s -> Tuple s a

  open StateL

  record StateR (s a : Set) : Set where
    constructor stateR:
    field runStateR : s -> Tuple s a

  open StateR

  instance
    FunctorStateL : Functor (StateL s)
    FunctorStateL .map f (stateL: t) = stateL: λ s0 ->
      let (s1 , x) = t s0 in (s1 , f x)

    FunctorStateR : Functor (StateR s)
    FunctorStateR .map f (stateR: t) = stateR: λ s0 ->
      let (s1 , x) = t s0 in (s1 , f x)

    ApplicativeStateL : Applicative (StateL s)
    ApplicativeStateL .pure x = stateL: λ s -> (s , x)
    ApplicativeStateL ._<*>_ (stateL: f) (stateL: t) = stateL: λ s0 ->
      let (s1 , f') = f s0; (s2 , x) = t s1 in (s2 , f' x)

    ApplicativeStateR : Applicative (StateR s)
    ApplicativeStateR .pure x = stateR: λ s -> (s , x)
    ApplicativeStateR ._<*>_ (stateR: f) (stateR: t) = stateR: λ s0 ->
      let (s1 , x) = t s0; (s2 , f') = f s1 in (s2 , f' x)

record Traversable (t : Set -> Set) : Set where
  field
    {{superFunctor}} : Functor t
    {{superFoldable}} : Foldable t
    traverse : {{_ : Applicative f}} -> (a -> f b) -> t a -> f (t b)

  sequence : {{_ : Applicative f}} -> t (f a) -> f (t a)
  sequence = traverse id

  for : {{_ : Applicative f}} -> t a -> (a -> f b) -> f (t b)
  for = flip traverse

  mapAccumL : (a -> b -> Tuple a c) -> a -> t b -> Tuple a (t c)
  mapAccumL f a xs = runStateL (traverse (stateL: ∘ flip f) xs) a

  mapAccumR : (a -> b -> Tuple a c) -> a -> t b -> Tuple a (t c)
  mapAccumR f a xs = runStateR (traverse (stateR: ∘ flip f) xs) a

  scanl : {{_ : Buildable t}} -> (b -> a -> b) -> b -> t a -> t b
  scanl f b0 xs = uncurry (flip snoc) (mapAccumL (λ b a -> (f b a , b)) b0 xs)

  scanr : {{_ : Buildable t}} -> (a -> b -> b) -> b -> t a -> t b
  scanr f b0 xs = uncurry cons (mapAccumR (λ b a -> (f a b , b)) b0 xs)

open Traversable {{...}} public

instance
  TraversableMaybe : Traversable Maybe
  TraversableMaybe .traverse f = λ where
    Nothing -> pure Nothing
    (Just x) -> map Just (f x)

  TraversableList : Traversable List
  TraversableList .traverse f = listrec (pure []) λ where
    x _ ys -> (| _::_ (f x) ys |)

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
showString = _++_

showParen : Bool -> ShowS -> ShowS
showParen b p = if b then showString "(" ∘ p ∘ showString ")" else p

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
  ShowVoid : Show Void
  ShowVoid .showsPrec _ ()

  ShowUnit : Show Unit
  ShowUnit .showsPrec _ unit = showString "unit"

  ShowBool : Show Bool
  ShowBool .showsPrec _ True = showString "True"
  ShowBool .showsPrec _ False = showString "False"

  ShowNat : Show Nat
  ShowNat .showsPrec _ = showString ∘ primShowNat

  ShowInt : Show Int
  ShowInt .showsPrec _ = showString ∘ primShowInteger

  ShowFloat : Show Float
  ShowFloat .showsPrec _ = showString ∘ primShowFloat

  ShowChar : Show Char
  ShowChar .showsPrec _ = showString ∘ primShowChar

  ShowString : Show String
  ShowString .showsPrec _ = showString ∘ primShowString

  ShowTuple : {{_ : Show a}} {{_ : Show b}} -> Show (Tuple a b)
  ShowTuple .showsPrec d (x , y) = showString "(" ∘ showsPrec d x
    ∘ showString " , " ∘ showsPrec d y ∘ showString ")"

  ShowEither : {{_ : Show a}} {{_ : Show b}} -> Show (Either a b)
  ShowEither .showsPrec d (Left x) = showParen (d > appPrec) $
    showString "Left " ∘ showsPrec appPrec+1 x
  ShowEither .showsPrec d (Right x) = showParen (d > appPrec) $
    showString "Right " ∘ showsPrec appPrec+1 x

  ShowMaybe : {{_ : Show a}} -> Show (Maybe a)
  ShowMaybe .showsPrec d (Just x) = showParen (d > appPrec) $
    showString "Just " ∘ showsPrec appPrec+1 x
  ShowMaybe .showsPrec d Nothing = showString "Nothing"

  ShowList : {{_ : Show a}} -> Show (List a)
  ShowList {a = a} .showsPrec _ zs s' = listShow shows zs s'
    where
      listShow : (a -> ShowS) -> List a -> ShowS
      listShow _ [] s = "[]" ++ s
      listShow showx (x :: xs) s = "[ " ++ showx x (showl xs)
        where
          showl : List a -> String
          showl [] = " ]" ++ s
          showl (y :: ys) = " , " ++ showx y (showl ys)

  ShowIdentity : {{_ : Show a}} -> Show (Identity a)
  ShowIdentity .showsPrec d (Identity: x) = showParen (d > appPrec) $
    showString "Identity: " ∘ showsPrec appPrec+1 x

  ShowConst : {{_ : Show a}} -> Show (Const a b)
  ShowConst .showsPrec d (Const: x) = showParen (d > appPrec) $
    showString "Const: " ∘ showsPrec appPrec+1 x

  ShowSum : {{_ : Show a}} -> Show (Sum a)
  ShowSum .showsPrec d (Sum: x) = showParen (d > appPrec) $
    showString "Show: " ∘ showsPrec appPrec+1 x

  ShowProduct : {{_ : Show a}} -> Show (Product a)
  ShowProduct .showsPrec d (Product: x) = showParen (d > appPrec) $
    showString "Product: " ∘ showsPrec appPrec+1 x

  ShowDual : {{_ : Show a}} -> Show (Dual a)
  ShowDual .showsPrec d (Dual: x) = showParen (d > appPrec) $
    showString "Dual: " ∘ showsPrec appPrec+1 x

  ShowFirst : {{_ : Show a}} -> Show (First a)
  ShowFirst .showsPrec d (First: x) = showParen (d > appPrec) $
    showString "First: " ∘ showsPrec appPrec+1 x

  ShowLast : {{_ : Show a}} -> Show (Last a)
  ShowLast .showsPrec d (Last: x) = showParen (d > appPrec) $
    showString "Last: " ∘ showsPrec appPrec+1 x

  ShowMin : {{_ : Show a}} -> Show (Min a)
  ShowMin .showsPrec d (Min: x) = showParen (d > appPrec) $
    showString "Min: " ∘ showsPrec appPrec+1 x

  ShowMax : {{_ : Show a}} -> Show (Max a)
  ShowMax .showsPrec d (Max: x) = showParen (d > appPrec) $
    showString "Max: " ∘ showsPrec appPrec+1 x

  ShowAny : Show Any
  ShowAny .showsPrec d (Any: x) = showParen (d > appPrec) $
    showString "Any: " ∘ showsPrec appPrec+1 x

  ShowAll : Show All
  ShowAll .showsPrec d (All: x) = showParen (d > appPrec) $
    showString "All: " ∘ showsPrec appPrec+1 x
