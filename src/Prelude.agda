{-# OPTIONS --type-in-type #-}

module Prelude where

private
  variable
    a b c d r s : Set
    f m : Set -> Set

--------------------------------------------------------------------------------
-- Primitive types and type constructors
--------------------------------------------------------------------------------

data Void : Set where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit; tt to unit)

open import Agda.Builtin.Bool public
  using (Bool)
  renaming (true to True; false to False)

open import Agda.Builtin.Nat public
  using (Nat)
  renaming (suc to Suc; zero to Zero)

open import Agda.Builtin.Int public
  using (Int)
  renaming (pos to Pos; negsuc to NegSuc)

open import Agda.Builtin.Float public
  using (Float)

open import Agda.Builtin.Char public
  using (Char)

open import Agda.Builtin.String public
  using (String)

Not : Set -> Set
Not a = a -> Void

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _===_)

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

open import Agda.Builtin.List public
  using (List; [])
  renaming (_∷_ to _::_)

open import Agda.Builtin.IO public
  using (IO)

--------------------------------------------------------------------------------
-- Wrappers
--------------------------------------------------------------------------------

record Identity (a : Set) : Set where
  constructor Identity:
  field runIdentity : a

open Identity public

record Const (a b : Set) : Set where
  constructor Const:
  field getConst : a

open Const public

-- Endofunctions
record Endo a : Set where
  constructor Endo:
  field appEndo : a -> a

open Endo public

--------------------------------------------------------------------------------
-- Primitive functions and operations
--------------------------------------------------------------------------------

open import Agda.Builtin.TrustMe public
  renaming (primTrustMe to trustMe)

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
_$_ = id

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

open Agda.Builtin.Float public
  renaming (
    primNatToFloat to natToFloat;
    primFloatSqrt to sqrt;
    primRound to round;
    primFloor to floor;
    primCeiling to ceil;
    primExp to exp;
    primLog to log;
    primSin to sin;
    primCos to cos;
    primTan to tan;
    primASin to asin;
    primACos to acos;
    primATan to atan;
    primATan2 to atan2
  )

intToFloat : Int -> Float
intToFloat (Pos n) = natToFloat n
intToFloat (NegSuc n) = Agda.Builtin.Float.primFloatMinus -1.0 (natToFloat n)

open Agda.Builtin.Char public
  renaming (
    primIsLower to isLower;
    primIsDigit to isDigit;
    primIsAlpha to isAlpha;
    primIsSpace to isSpace;
    primIsAscii to isAscii;
    primIsLatin1 to isLatin1;
    primIsPrint to isPrint;
    primIsHexDigit to isHexDigit;
    primToUpper to toUpper;
    primToLower to toLower;
    primCharToNat to ord;
    primNatToChar to chr
  )

open Agda.Builtin.String public
  renaming (
    primStringToList to unpack;
    primStringFromList to pack
  )

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
maybeToRight b = mirror ∘ maybeToLeft b

leftToMaybe : Either a b -> Maybe a
leftToMaybe = either Just (const Nothing)

RightToMaybe : Either a b -> Maybe b
RightToMaybe = leftToMaybe ∘ mirror

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

postulate
  putStr : String -> IO Unit
  putStrLn : String -> IO Unit
  getLine : IO String
  getContents : IO String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC mapIO = \ _ _ -> fmap #-}
{-# COMPILE GHC pureIO = \ _ -> pure #-}
{-# COMPILE GHC apIO = \ _ _ -> (<*>) #-}
{-# COMPILE GHC bindIO = \ _ _ -> (>>=) #-}
{-# COMPILE GHC putStr = Text.putStr #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC getContents = Text.getContents #-}

--------------------------------------------------------------------------------
-- Boolean
--------------------------------------------------------------------------------

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
  booleanBool : Boolean Bool
  booleanBool .ff = False
  booleanBool .tt = True
  booleanBool .not = λ where
    False -> True
    True -> False
  booleanBool ._||_ = λ where
    False b -> b
    True _ -> True
  booleanBool ._&&_ = λ where
    False _ -> False
    True b -> b

  booleanFunction : {{_ : Boolean b}} -> Boolean (a -> b)
  booleanFunction .ff = const ff
  booleanFunction .tt = const tt
  booleanFunction .not f = not ∘ f
  booleanFunction ._||_ f g a = f a || g a
  booleanFunction ._&&_ f g a = f a && g a

--------------------------------------------------------------------------------
-- Eq
--------------------------------------------------------------------------------

record Eq (a : Set) : Set where
  infix 4 _==_
  field _==_ : a -> a -> Bool

  infix 4 _/=_
  _/=_ : a -> a -> Bool
  a /= a' = if a == a' then False else True

open Eq {{...}} public

instance
  eqVoid : Eq Void
  eqVoid ._==_ = λ ()

  eqUnit : Eq Unit
  eqUnit ._==_ unit unit = True

  eqBool : Eq Bool
  eqBool ._==_ = λ where
    True True -> True
    False False -> False
    _ _ -> False

  eqNat : Eq Nat
  eqNat ._==_ = Agda.Builtin.Nat._==_

  eqInt : Eq Int
  eqInt ._==_ = λ where
    (Pos m) (Pos n) -> m == n
    (NegSuc m) (NegSuc n) -> m == n
    _ _ -> False

  eqFloat : Eq Float
  eqFloat ._==_ = Agda.Builtin.Float.primFloatNumericalEquality

  eqChar : Eq Char
  eqChar ._==_ = Agda.Builtin.Char.primCharEquality

  eqString : Eq String
  eqString ._==_ = Agda.Builtin.String.primStringEquality

  eqEither : {{_ : Eq a}} {{_ : Eq b}} -> Eq (Either a b)
  eqEither ._==_ = λ where
    (Left a) (Left a') -> a == a'
    (Right b) (Right b') -> b == b'
    _ _ -> False

  eqTuple : {{_ : Eq a}} {{_ : Eq b}} -> Eq (Tuple a b)
  eqTuple ._==_ (a , b) (a' , b') = (a == a') && (b == b')

  eqMaybe : {{_ : Eq a}} -> Eq (Maybe a)
  eqMaybe ._==_ = λ where
    Nothing Nothing -> True
    (Just a) (Just a') -> a == a'
    _ _ -> False

  eqList : {{_ : Eq a}} -> Eq (List a)
  eqList ._==_ = λ where
    [] [] -> True
    (a :: as) (a' :: as') -> a == a' && as == as'
    _ _ -> False

  eqIdentity : {{_ : Eq a}} -> Eq (Identity a)
  eqIdentity ._==_ (Identity: a) (Identity: a') = a == a'

  eqConst : {{_ : Eq a}} -> Eq (Const a b)
  eqConst ._==_ (Const: a) (Const: a') = a == a'

--------------------------------------------------------------------------------
-- Ord
--------------------------------------------------------------------------------

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (a : Set) : Set where
  infixl 4 _<_
  field
    overlap {{super}} : Eq a
    _<_ : a -> a -> Bool

  compare : a -> a -> Ordering
  compare a a' = if a < a' then LT else if a == a' then EQ else GT

  infixl 4 _<=_
  _<=_ : a -> a -> Bool
  a <= a' = if a < a' then True else if a == a' then True else False

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
  comparing p b b' = compare (p b) (p b')

open Ord {{...}} public

instance
  ordVoid : Ord Void
  ordVoid ._<_ = λ ()

  ordUnit : Ord Unit
  ordUnit ._<_ unit unit = False

  ordBool : Ord Bool
  ordBool ._<_ = λ where
    False True -> True
    _ _ -> False

  ordNat : Ord Nat
  ordNat ._<_ = Agda.Builtin.Nat._<_

  ordInt : Ord Int
  ordInt ._<_ = λ where
    (Pos m) (Pos n) -> m < n
    (NegSuc m) (NegSuc n) -> m > n
    (NegSuc _) (Pos _) -> True
    (Pos _) (NegSuc _) -> False

  ordFloat : Ord Float
  ordFloat ._<_ = Agda.Builtin.Float.primFloatNumericalLess

  ordChar : Ord Char
  ordChar ._<_ c c' = ord c < ord c'

  ordList : {{_ : Ord a}} -> Ord (List a)
  ordList ._<_ = λ where
    (a :: as) (a' :: as') -> a < a' || (a == a' && as < as')
    [] [] -> True
    _ _ -> False

  ordString : Ord String
  ordString ._<_ s s' with unpack s | unpack s'
  ... | (c :: cs) | (c' :: cs') = c < c' || (c == c' && cs < cs')
  ... | _ | _ = False

  ordTuple : {{_ : Ord a}} {{_ : Ord b}} -> Ord (Tuple a b)
  ordTuple ._<_ (a , b) (a' , b') = a < a' || (a == a' && b < b')

  ordMaybe : {{_ : Ord a}} -> Ord (Maybe a)
  ordMaybe ._<_ = λ where
    _ Nothing -> False
    Nothing _ -> True
    (Just a) (Just a') -> a < a'

  ordIdentity : {{_ : Ord a}} -> Ord (Identity a)
  ordIdentity ._<_ (Identity: a) (Identity: a') = a < a'

  ordConst : {{_ : Ord a}} -> Ord (Const a b)
  ordConst ._<_ (Const: a) (Const: a') = a < a'

--------------------------------------------------------------------------------
-- FromNat and FromNeg
--------------------------------------------------------------------------------

open import Agda.Builtin.FromNat public
  renaming (Number to FromNat)
  using (fromNat)

open import Agda.Builtin.FromNeg public
  renaming (Negative to FromNeg)
  using (fromNeg)

instance
  fromNatNat : FromNat Nat
  fromNatNat = record {
      Constraint = const Unit;
      fromNat = λ n -> n
    }

  fromNatInt : FromNat Int
  fromNatInt = record {
      Constraint = const Unit;
      fromNat = λ n -> Pos n
    }

  fromNegInt : FromNeg Int
  fromNegInt = record {
      Constraint = const Unit;
      fromNeg = λ n -> neg n
    }

  fromNegFloat : FromNeg Float
  fromNegFloat = record {
      Constraint = const Unit;
      fromNeg = λ x -> Agda.Builtin.Float.primFloatNegate (natToFloat x)
    }

--------------------------------------------------------------------------------
-- Arithmetic operations
--------------------------------------------------------------------------------

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
  additionSet : Addition Set
  additionSet ._+_ = Either

  multiplicationSet : Multiplication Set
  multiplicationSet ._*_ = Tuple

  powerSet : Power Set
  powerSet ._^_ a = λ where
    0 -> Unit
    1 -> a
    (Suc n) -> a ^ n * a

  additionNat : Addition Nat
  additionNat ._+_ = Agda.Builtin.Nat._+_

  multiplicationNat : Multiplication Nat
  multiplicationNat ._*_ = Agda.Builtin.Nat._*_

  powerNat : Power Nat
  powerNat ._^_ a = λ where
    0 -> 1
    1 -> a
    (Suc n) -> a ^ n * a

  exponentiationNat : Exponentiation Nat
  exponentiationNat ._**_ = _^_

  subtractionNat : Subtraction Nat
  subtractionNat ._-_ = Agda.Builtin.Nat._-_

  divisionNat : Division Nat
  divisionNat .DivisionConstraint n = Assert (n > 0)
  divisionNat ._/_ m (Suc n) = divAux 0 n m n
    where divAux = Agda.Builtin.Nat.div-helper

  modulusNat : Modulus Nat
  modulusNat .ModulusConstraint n = Assert (n > 0)
  modulusNat ._%_ m (Suc n) = modAux 0 n m n
    where modAux = Agda.Builtin.Nat.mod-helper

  additionInt : Addition Int
  additionInt ._+_ = add
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

  multiplicationInt : Multiplication Int
  multiplicationInt ._*_ = λ where
    (Pos n) (Pos m) -> Pos (n * m)
    (NegSuc n) (NegSuc m) -> Pos (Suc n * Suc m)
    (Pos n) (NegSuc m) -> neg (n * Suc m)
    (NegSuc n) (Pos m) -> neg (Suc n * m)

  powerInt : Power Int
  powerInt ._^_ a = λ where
    0 -> 1
    1 -> a
    (Suc n) -> a ^ n * a

  negationInt : Negation Int
  negationInt .-_ = λ where
    (Pos 0) -> Pos 0
    (Pos (Suc n)) -> NegSuc n
    (NegSuc n) -> Pos (Suc n)

  subtractionInt : Subtraction Int
  subtractionInt ._-_ m n = m + (- n)

  divisionInt : Division Int
  divisionInt .DivisionConstraint n = Assert (n > 0)
  divisionInt ._/_ x y with x | y
  ... | Pos m | Pos (Suc n) = Pos (m / Suc n)
  ... | NegSuc m | Pos (Suc n) = neg (Suc m / Suc n)
  ... | Pos m | NegSuc n = neg (m / Suc n)
  ... | NegSuc m | NegSuc n = Pos (Suc m / Suc n)

  modulusInt : Modulus Int
  modulusInt .ModulusConstraint n = Assert (n > 0)
  modulusInt ._%_ x y with x | y
  ... | Pos m | Pos (Suc n) = Pos (m % Suc n)
  ... | NegSuc m | Pos (Suc n) = neg (Suc m % Suc n)
  ... | Pos m | NegSuc n = Pos (m % Suc n)
  ... | NegSuc m | NegSuc n = neg (Suc m % Suc n)

  signedInt : Signed Int
  signedInt .abs = λ where
    (Pos n) -> Pos n
    (NegSuc n) -> Pos (Suc n)
  signedInt .signum = λ where
    (Pos 0) -> Pos 0
    (Pos (Suc _)) -> Pos 1
    (NegSuc _) -> NegSuc 0

  additionFloat : Addition Float
  additionFloat ._+_ = Agda.Builtin.Float.primFloatPlus

  multiplicationFloat : Multiplication Float
  multiplicationFloat ._*_ = Agda.Builtin.Float.primFloatTimes

  powerFloat : Power Float
  powerFloat ._^_ a = λ where
    0 -> 1.0
    1 -> a
    (Suc n) -> a ^ n * a

  exponentiationFloat : Exponentiation Float
  exponentiationFloat ._**_ x y = exp (y * log x)

  negationFloat : Negation Float
  negationFloat .-_ = Agda.Builtin.Float.primFloatNegate

  subtractionFloat : Subtraction Float
  subtractionFloat ._-_ = Agda.Builtin.Float.primFloatMinus

  divisionFloat : Division Float
  divisionFloat .DivisionConstraint = const Unit
  divisionFloat ._/_ x y = Agda.Builtin.Float.primFloatDiv x y

  signedFloat : Signed Float
  signedFloat .abs x = if x < 0.0 then - x else x
  signedFloat .signum x with compare x 0.0
  ... | EQ = 0.0
  ... | LT = -1.0
  ... | GT = 1.0

  additionFunction : {{_ : Addition b}} -> Addition (a -> b)
  additionFunction ._+_ f g x = f x + g x

  multiplicationFunction : {{_ : Multiplication b}} -> Multiplication (a -> b)
  multiplicationFunction ._*_ f g x = f x * g x

  negationFunction : {{_ : Negation b}} -> Negation (a -> b)
  negationFunction .-_ f x = - (f x)

  subtractionFunction : {{_ : Subtraction b}} -> Subtraction (a -> b)
  subtractionFunction ._-_ f g x = f x - g x

  powerFunction : Power (a -> a)
  powerFunction ._^_ f = λ where
    0 -> id
    1 -> f
    (Suc n) -> f ^ n ∘ f

--------------------------------------------------------------------------------
-- Semigroup
--------------------------------------------------------------------------------

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
  semigroupDual : {{_ : Semigroup a}} -> Semigroup (Dual a)
  semigroupDual ._<>_ (Dual: a) (Dual: a') = Dual: (a' <> a)

  semigroupFirst : Semigroup (First a)
  semigroupFirst ._<>_ a _ = a

  semigroupLast : Semigroup (Last a)
  semigroupLast ._<>_ _ a = a

  semigroupMin : {{_ : Ord a}} -> Semigroup (Min a)
  semigroupMin ._<>_ (Min: a) (Min: a') = Min: (min a a')

  semigroupMax : {{_ : Ord a}} -> Semigroup (Max a)
  semigroupMax ._<>_ (Max: a) (Max: a') = Max: (max a a')

  semigroupAny : Semigroup Any
  semigroupAny ._<>_ (Any: b) (Any: b') = Any: (b || b')

  semigroupAll : Semigroup All
  semigroupAll ._<>_ (All: b) (All: b') = All: (b && b')

  semigroupVoid : Semigroup Void
  semigroupVoid ._<>_ = λ ()

  semigroupUnit : Semigroup Unit
  semigroupUnit ._<>_ unit unit = unit

  semigroupSumNat : Semigroup (Sum Nat)
  semigroupSumNat ._<>_ (Sum: m) (Sum: n) = Sum: (m + n)

  semigroupProductNat : Semigroup (Product Nat)
  semigroupProductNat ._<>_ (Product: x) (Product: y) = Product: (x * y)

  semigroupSumInt : Semigroup (Sum Int)
  semigroupSumInt ._<>_ (Sum: m) (Sum: n) = Sum: (m + n)

  semigroupProductInt : Semigroup (Product Int)
  semigroupProductInt ._<>_ (Product: x) (Product: y) = Product: (x * y)

  semigroupString : Semigroup String
  semigroupString ._<>_ = Agda.Builtin.String.primStringAppend

  semigroupFunction : {{_ : Semigroup b}} -> Semigroup (a -> b)
  semigroupFunction ._<>_ f g = λ a -> f a <> g a

  semigroupEither : {{_ : Semigroup a}} {{_ : Semigroup b}}
    -> Semigroup (Either a b)
  semigroupEither ._<>_ (Left _) b = b
  semigroupEither ._<>_ a _ = a

  semigroupTuple : {{_ : Semigroup a}} {{_ : Semigroup b}}
    -> Semigroup (Tuple a b)
  semigroupTuple ._<>_ (a , b) (a' , b') = (a <> a' , b <> b')

  semigroupMaybe : {{_ : Semigroup a}} -> Semigroup (Maybe a)
  semigroupMaybe ._<>_ = λ where
    Nothing m -> m
    m Nothing -> m
    (Just a) (Just a') -> Just (a <> a')

  semigroupList : Semigroup (List a)
  semigroupList ._<>_ as as' = listrec as' (λ x _ xs -> x :: xs) as

  semigroupIO : {{_ : Semigroup a}} -> Semigroup (IO a)
  semigroupIO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

  semigroupIdentity : {{_ : Semigroup a}} -> Semigroup (Identity a)
  semigroupIdentity ._<>_ (Identity: a) (Identity: a') =
    Identity: (a <> a')

  semigroupConst : {{_ : Semigroup a}} -> Semigroup (Const a b)
  semigroupConst ._<>_ (Const: a) (Const: a') = Const: (a <> a')

  semigroupEndo : Semigroup (Endo a)
  semigroupEndo ._<>_ g f = Endo: (appEndo g ∘ appEndo f)

--------------------------------------------------------------------------------
-- Monoid
--------------------------------------------------------------------------------

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
  monoidDual : {{_ : Monoid a}} -> Monoid (Dual a)
  monoidDual .neutral = Dual: neutral

  monoidFirst : {{_ : Monoid a}} -> Monoid (First a)
  monoidFirst .neutral = First: neutral

  monoidLast : {{_ : Monoid a}} -> Monoid (Last a)
  monoidLast .neutral = Last: neutral

  monoidUnit : Monoid Unit
  monoidUnit .neutral = unit

  monoidAll : Monoid All
  monoidAll .neutral = All: True

  monoidAny : Monoid Any
  monoidAny .neutral = Any: False

  monoidSumNat : Monoid (Sum Nat)
  monoidSumNat .neutral = Sum: 0

  monoidProductNat : Monoid (Product Nat)
  monoidProductNat .neutral = Product: (Suc 0)

  monoidSumInt : Monoid (Sum Int)
  monoidSumInt .neutral = Sum: 0

  monoidProductInt : Monoid (Product Int)
  monoidProductInt .neutral = Product: 1

  monoidString : Monoid String
  monoidString .neutral = ""

  monoidFunction : {{_ : Monoid b}} -> Monoid (a -> b)
  monoidFunction .neutral = const neutral

  monoidEndo : Monoid (Endo a)
  monoidEndo .neutral = Endo: id

  monoidMaybe : {{_ : Semigroup a}} -> Monoid (Maybe a)
  monoidMaybe .neutral = Nothing

  monoidList : Monoid (List a)
  monoidList .neutral = []

  monoidIO : {{_ : Monoid a}} -> Monoid (IO a)
  monoidIO .neutral = pureIO neutral

  monoidIdentity : {{_ : Monoid a}} -> Monoid (Identity a)
  monoidIdentity .neutral = Identity: neutral

  monoidConst : {{_ : Monoid a}} -> Monoid (Const a b)
  monoidConst .neutral = Const: neutral

--------------------------------------------------------------------------------
-- IsBuildable, buildable
--------------------------------------------------------------------------------

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

{-# TERMINATING #-}
unfoldr : {{_ : IsBuildable s a}} -> (b -> Maybe (Tuple a b)) -> b -> s
unfoldr f b with f b
... | Nothing = nil
... | (Just (a , b')) = cons a (unfoldr f b')

{-# TERMINATING #-}
unfoldl : {{_ : IsBuildable s a}} -> (b -> Maybe (Tuple b a)) -> b -> s
unfoldl f b with f b
... | Nothing = nil
... | (Just (b' , a)) = snoc (unfoldl f b') a

instance
  buildableList : Buildable List
  buildableList .singleton = _:: []

  isBuildableStringChar : IsBuildable String Char
  isBuildableStringChar .singleton = pack ∘ singleton

--------------------------------------------------------------------------------
-- Functor, Contravariant, bifunctor, Profunctor
--------------------------------------------------------------------------------

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
  profunctorFunction : Profunctor Function
  profunctorFunction .dimap f g h = g ∘ h ∘ f

  bifunctorEither : Bifunctor Either
  bifunctorEither .bimap f g = either (Left ∘ f) (Right ∘ g)

  functorEither : Functor (Either a)
  functorEither .map = second

  bifunctorTuple : Bifunctor Tuple
  bifunctorTuple .bimap f g = tuple (f ∘ fst) (g ∘ snd)

  functorTuple : Functor (Tuple a)
  functorTuple .map = second

  functorMaybe : Functor Maybe
  functorMaybe .map f = λ where
    Nothing -> Nothing
    (Just a) -> Just (f a)

  functorList : Functor List
  functorList .map f = listrec [] λ a _ bs -> f a :: bs

  functorIO : Functor IO
  functorIO .map = mapIO

  functorIdentity : Functor Identity
  functorIdentity .map f = Identity: ∘ f ∘ runIdentity

  bifunctorConst : Bifunctor Const
  bifunctorConst .bimap f g = Const: ∘ f ∘ getConst

  functorConst : Functor (Const a)
  functorConst .map = second

  contravariantConst : Contravariant (Const a)
  contravariantConst .contramap f = Const: ∘ getConst

  functorSum : Functor Sum
  functorSum .map f = Sum: ∘ f ∘ getSum

  functorProduct : Functor Product
  functorProduct .map f = Product: ∘ f ∘ getProduct

  functorDual : Functor Dual
  functorDual .map f = Dual: ∘ f ∘ getDual

  functorFirst : Functor First
  functorFirst .map f = First: ∘ f ∘ getFirst

  functorLast : Functor Last
  functorLast .map f = Last: ∘ f ∘ getLast

  functorMin : Functor Min
  functorMin .map f = Min: ∘ f ∘ getMin

  functorMax : Functor Max
  functorMax .map f = Max: ∘ f ∘ getMax

--------------------------------------------------------------------------------
-- applicative
--------------------------------------------------------------------------------

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

{-# NON_TERMINATING #-}
forever : {{_ : Applicative f}} -> f a -> f b
forever as = as *> forever as

instance
  applicativeEither : Applicative (Either a)
  applicativeEither .pure = Right
  applicativeEither ._<*>_ = λ where
    (Left a) _ -> Left a
    (Right f) -> map f

  applicativeMaybe : Applicative Maybe
  applicativeMaybe .pure = Just
  applicativeMaybe ._<*>_ = λ where
    (Just f) -> map f
    Nothing _ -> Nothing

  applicativeList : Applicative List
  applicativeList .pure = singleton
  applicativeList ._<*>_ = λ where
    [] _ -> []
    _ [] -> []
    (f :: fs) (x :: xs) -> f x :: (fs <*> xs)

  applicativeIO : Applicative IO
  applicativeIO .pure = pureIO
  applicativeIO ._<*>_ = apIO

  applicativeIdentity : Applicative Identity
  applicativeIdentity .pure = Identity:
  applicativeIdentity ._<*>_ = map ∘ runIdentity

  applicativeConst : {{_ : Monoid a}} -> Applicative (Const a)
  applicativeConst .pure _ = Const: neutral
  applicativeConst ._<*>_ (Const: f) (Const: a) = Const: (f <> a)

  applicativeSum : Applicative Sum
  applicativeSum .pure = Sum:
  applicativeSum ._<*>_ (Sum: f) (Sum: x) = Sum: (f x)

  applicativeProduct : Applicative Product
  applicativeProduct .pure = Product:
  applicativeProduct ._<*>_ (Product: f) (Product: x) = Product: (f x)

  applicativeDual : Applicative Dual
  applicativeDual .pure = Dual:
  applicativeDual ._<*>_ (Dual: f) (Dual: x) = Dual: (f x)

  applicativeFirst : Applicative First
  applicativeFirst .pure = First:
  applicativeFirst ._<*>_ (First: f) (First: x) = First: (f x)

  applicativeLast : Applicative Last
  applicativeLast .pure = Last:
  applicativeLast ._<*>_ (Last: f) (Last: x) = Last: (f x)

  applicativeMin : Applicative Min
  applicativeMin .pure = Min:
  applicativeMin ._<*>_ (Min: f) (Min: x) = Min: (f x)

  applicativeMax : Applicative Max
  applicativeMax .pure = Max:
  applicativeMax ._<*>_ (Max: f) (Max: x) = Max: (f x)

--------------------------------------------------------------------------------
-- alternative
--------------------------------------------------------------------------------

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
  alternativeMaybe : Alternative Maybe
  alternativeMaybe .empty = Nothing
  alternativeMaybe ._<|>_ = λ where
    Nothing r -> r
    l _ -> l

  alternativeList : Alternative List
  alternativeList .empty = neutral
  alternativeList ._<|>_ = _<>_

--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

record Monad (M : Set -> Set) : Set where
  infixl 1 _>>=_
  field
    overlap {{super}} : Applicative M
    _>>=_ : M a -> (a -> M b) -> M b

  join : M (M a) -> M a
  join = _>>= id

  infixl 1 _>>_
  _>>_ : M a -> M b -> M b
  _>>_ = _*>_

open Monad {{...}} public

return : forall {a m} {{_ : Monad m}} -> a -> m a
return = pure

instance
  monadEither : Monad (Either a)
  monadEither ._>>=_ = λ where
    (Left a) _ -> Left a
    (Right x) k -> k x

  monadMaybe : Monad Maybe
  monadMaybe ._>>=_ = λ where
    Nothing _ -> Nothing
    (Just x) k -> k x

  monadList : Monad List
  monadList ._>>=_ = λ where
    [] k -> []
    (x :: xs) k -> k x ++ (xs >>= k)

  monadIO : Monad IO
  monadIO ._>>=_ = bindIO

  monadIdentity : Monad Identity
  monadIdentity ._>>=_ (Identity: x) k = k x

  monadSum : Monad Sum
  monadSum ._>>=_ (Sum: x) k = k x

  monadProduct : Monad Product
  monadProduct ._>>=_ (Product: x) k = k x

  monadDual : Monad Dual
  monadDual ._>>=_ (Dual: x) k = k x

  monadFirst : Monad First
  monadFirst ._>>=_ (First: x) k = k x

  monadLast : Monad Last
  monadLast ._>>=_ (Last: x) k = k x

  monadMin : Monad Min
  monadMin ._>>=_ (Min: x) k = k x

  monadMax : Monad Max
  monadMax ._>>=_ (Max: x) k = k x

--------------------------------------------------------------------------------
-- IsFoldable, Foldable
--------------------------------------------------------------------------------

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

  notNull : s -> Bool
  notNull = any (const True)

  Nonempty : s -> Set
  Nonempty = Assert ∘ notNull

  null : s -> Bool
  null = not ∘ notNull

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

Foldable : (Set -> Set) -> Set
Foldable f = forall {a} -> IsFoldable (f a) a

instance
  isFoldableNatUnit : IsFoldable Nat Unit
  isFoldableNatUnit .foldMap b 0 = neutral
  isFoldableNatUnit .foldMap b (Suc n) = b unit <> foldMap b n

  foldableEither : Foldable (Either a)
  foldableEither .foldMap _ (Left _) = neutral
  foldableEither .foldMap f (Right x) = f x

  foldableTuple : Foldable (Tuple a)
  foldableTuple .foldMap f (_ , x) = f x

  foldableMaybe : Foldable Maybe
  foldableMaybe .foldMap = maybe neutral

  foldableList : Foldable List
  foldableList .foldMap f = listrec neutral λ x _ y -> f x <> y

  isFoldableStringChar : IsFoldable String Char
  isFoldableStringChar .foldMap f = foldMap f ∘ unpack

--------------------------------------------------------------------------------
-- IsFoldable1, Foldable1
--------------------------------------------------------------------------------

record IsFoldable1 (s a : Set) : Set where
  field {{isFoldable}} : IsFoldable s a

  foldMap1 : {{_ : Semigroup b}}
    -> (a -> b) -> (s : s) {{_ : Nonempty s}} -> b
  foldMap1 f s = fromJust (foldMap (Just ∘ f) s) {{believeMe}}

  fold1 : {{_ : Semigroup a}} (s : s) {{_ : Nonempty s}} -> a
  fold1 s = fromJust (foldMap Just s) {{believeMe}}

  foldr1 : (a -> a -> a) -> (s : s) {{_ : Nonempty s}} -> a
  foldr1 f s = fromJust (foldr g Nothing s) {{believeMe}}
    where
      g : a -> Maybe a -> Maybe a
      g a Nothing = Just a
      g a (Just a') = Just (f a a')

  foldl1 : (a -> a -> a) -> (s : s) {{_ : Nonempty s}} -> a
  foldl1 f s = fromJust (foldl g Nothing s) {{believeMe}}
    where
      g : Maybe a -> a -> Maybe a
      g Nothing a = Just a
      g (Just a) a' = Just (f a a')

  module _ {{_ : Ord a}} where

    minimum : (s : s) {{_ : Nonempty s}} -> a
    minimum = foldr1 min

    maximum : (s : s) {{_ : Nonempty s}} -> a
    maximum = foldr1 max

open IsFoldable1 {{...}} public

Foldable1 : (Set -> Set) -> Set
Foldable1 f = forall {a} -> IsFoldable1 (f a) a

instance
  isFoldable1 : {{_ : IsFoldable s a}} -> IsFoldable1 s a
  isFoldable1 = record {}

--------------------------------------------------------------------------------
-- Traversable
--------------------------------------------------------------------------------

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
    functorStateL : Functor (StateL s)
    functorStateL .map f (stateL: t) = stateL: λ s0 ->
      let (s1 , x) = t s0 in (s1 , f x)

    functorStateR : Functor (StateR s)
    functorStateR .map f (stateR: t) = stateR: λ s0 ->
      let (s1 , x) = t s0 in (s1 , f x)

    applicativeStateL : Applicative (StateL s)
    applicativeStateL .pure x = stateL: λ s -> (s , x)
    applicativeStateL ._<*>_ (stateL: f) (stateL: t) = stateL: λ s0 ->
      let (s1 , f') = f s0; (s2 , x) = t s1 in (s2 , f' x)

    applicativeStateR : Applicative (StateR s)
    applicativeStateR .pure x = stateR: λ s -> (s , x)
    applicativeStateR ._<*>_ (stateR: f) (stateR: t) = stateR: λ s0 ->
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
  traversableEither : Traversable (Either a)
  traversableEither .traverse f = λ where
    (Left a) -> pure (Left a)
    (Right x) -> map Right (f x)

  traversableTuple : Traversable (Tuple a)
  traversableTuple .traverse f (a , x) = map (a ,_) (f x)

  traversableMaybe : Traversable Maybe
  traversableMaybe .traverse f = λ where
    Nothing -> pure Nothing
    (Just x) -> map Just (f x)

  traversableList : Traversable List
  traversableList .traverse f = listrec (pure []) λ where
    x _ ys -> (| _::_ (f x) ys |)

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

record Show (a : Set) : Set where
  field show : a -> String

  print : a -> IO Unit
  print a = putStrLn (show a)

open Show {{...}} public

instance
  showVoid : Show Void
  showVoid .show ()

  showUnit : Show Unit
  showUnit .show unit = "unit"

  showBool : Show Bool
  showBool .show True = "True"
  showBool .show False = "False"

  showNat : Show Nat
  showNat .show = Agda.Builtin.String.primShowNat

  showInt : Show Int
  showInt .show = Agda.Builtin.Int.primShowInteger

  showFloat : Show Float
  showFloat .show = Agda.Builtin.Float.primShowFloat

  showChar : Show Char
  showChar .show = Agda.Builtin.String.primShowChar

  showString : Show String
  showString .show = Agda.Builtin.String.primShowString

  showTuple : {{_ : Show a}} {{_ : Show b}} -> Show (Tuple a b)
  showTuple .show (a , b) = "(" ++ show a ++ " , " ++ show b ++ ")"

  showEither : {{_ : Show a}} {{_ : Show b}} -> Show (Either a b)
  showEither .show = λ where
    (Left a) -> "(Left " ++ show a ++ ")"
    (Right b) -> "(Right " ++ show b ++ ")"

  showMaybe : {{_ : Show a}} -> Show (Maybe a)
  showMaybe .show = λ where
    (Just a) -> "(Just " ++ show a ++ ")"
    Nothing -> "Nothing"

  showList : {{_ : Show a}} -> Show (List a)
  showList .show [] = "[]"
  showList .show as = "[ " ++ show' as ++ " ]"
    where
      show' : {{_ : Show a}} -> List a -> String
      show' [] = ""
      show' (a :: []) = show a
      show' (a :: as) = show a ++ " , " ++ show' as

  showIdentity : {{_ : Show a}} -> Show (Identity a)
  showIdentity .show (Identity: a) = "(Identity: " ++ show a ++ ")"

  showConst : {{_ : Show a}} -> Show (Const a b)
  showConst .show (Const: a) = "(Const: " ++ show a ++ ")"

  showSum : {{_ : Show a}} -> Show (Sum a)
  showSum .show (Sum: a) = "(Sum: " ++ show a ++ ")"

  showProduct : {{_ : Show a}} -> Show (Product a)
  showProduct .show (Product: a) = "(Product: " ++ show a ++ ")"

  showDual : {{_ : Show a}} -> Show (Dual a)
  showDual .show (Dual: a) = "(Dual: " ++ show a ++ ")"

  showFirst : {{_ : Show a}} -> Show (First a)
  showFirst .show (First: a) = "(First: " ++ show a ++ ")"

  showLast : {{_ : Show a}} -> Show (Last a)
  showLast .show (Last: a) = "(Last: " ++ show a ++ ")"

  showMin : {{_ : Show a}} -> Show (Min a)
  showMin .show (Min: a) = "(Min: " ++ show a ++ ")"

  showMax : {{_ : Show a}} -> Show (Max a)
  showMax .show (Max: a) = "(Max: " ++ show a ++ ")"

  showAny : Show Any
  showAny .show (Any: a) = "(Any: " ++ show a ++ ")"

  showAll : Show All
  showAll .show (All: a) = "(All: " ++ show a ++ ")"
