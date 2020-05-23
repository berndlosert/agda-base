{-# OPTIONS --type-in-type #-}

module Prelude where

private
  variable
    A B C D R S : Set
    F M : Set -> Set

--------------------------------------------------------------------------------
-- Primitive types and type constructors
--------------------------------------------------------------------------------

data Void : Set where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit; tt to unit)

open import Agda.Builtin.Bool public
  using (Bool; true; false)

open import Agda.Builtin.Nat public
  using (Nat; suc; zero)

open import Agda.Builtin.Int public
  using (Int; pos; negsuc)

open import Agda.Builtin.Float public
  using (Float)

open import Agda.Builtin.Char public
  using (Char)

open import Agda.Builtin.String public
  using (String)

Not : Set -> Set
Not A = A -> Void

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _===_)

Function : Set -> Set -> Set
Function A B = A -> B

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

{-# COMPILE GHC Either = data Either (Left | Right) #-}

infixl 1 _,_
record Tuple (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Tuple public

{-# COMPILE GHC Tuple = data (,) ((,)) #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

open import Agda.Builtin.List public
  using (List; [])
  renaming (_∷_ to _::_)

open import Agda.Builtin.IO public
  using (IO)

--------------------------------------------------------------------------------
-- Wrappers
--------------------------------------------------------------------------------

record Identity (A : Set) : Set where
  constructor identity:
  field runIdentity : A

open Identity public

record Const (A B : Set) : Set where
  constructor const:
  field getConst : A

open Const public

-- Endofunctions
record Endo A : Set where
  constructor endo:
  field appEndo : A -> A

open Endo public

--------------------------------------------------------------------------------
-- Primitive functions and operations
--------------------------------------------------------------------------------

open import Agda.Builtin.TrustMe public
  renaming (primTrustMe to trustMe)

postulate
  believeMe : A
  error : String -> A

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC error = \ _ s -> error (Data.Text.unpack s) #-}

undefined : A
undefined = error "Prelude.undefined"

id : A -> A
id a = a

const : A -> B -> A
const a _ = a

flip : (A -> B -> C) -> B -> A -> C
flip f b a = f a b

infixr 0 _$_
_$_ : (A -> B) -> A -> B
_$_ = id

infixl 1 _#_
_#_ : A -> (A -> B) -> B
_#_ = flip _$_

case_of_ : A -> (A -> B) -> B
case_of_ = _#_

infixr 9 _<<<_
_<<<_ : (B -> C) -> (A -> B) -> A -> C
g <<< f = \ a -> g (f a)

infixr 9 _>>>_
_>>>_ : (A -> B) -> (B -> C) -> A -> C
_>>>_ = flip _<<<_

So : Bool -> Set
So false = Void
So true = Unit

infixr 10 if_then_else_
if_then_else_ : Bool -> A -> A -> A
if true then a else _ = a
if false then _ else a = a

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ 0 = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

applyN : (A -> A) -> Nat -> A -> A
applyN f n a = natrec a (const f) n

pred : Nat -> Nat
pred 0 = 0
pred (suc n) = n

neg : Nat -> Int
neg 0 = pos 0
neg (suc n) = negsuc n

foldZ : (Nat -> A) -> (Nat -> A) -> Int -> A
foldZ f g (pos n) = f n
foldZ f g (negsuc n) = g n

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
intToFloat (pos n) = natToFloat n
intToFloat (negsuc n) = Agda.Builtin.Float.primFloatMinus -1.0 (natToFloat n)

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

either : (A -> C) -> (B -> C) -> Either A B -> C
either f g (left a) = f a
either f g (right b) = g b

mirror : Either A B -> Either B A
mirror = either right left

untag : Either A A -> A
untag (left a) = a
untag (right a) = a

isLeft : Either A B -> Bool
isLeft (left _) = true
isLeft _ = false

isRight : Either A B -> Bool
isRight (left _) = false
isRight _ = true

fromLeft : A -> Either A B -> A
fromLeft _ (left a) = a
fromLeft a (right _) = a

fromRight : B -> Either A B -> B
fromRight b (left _) = b
fromRight _ (right b) = b

fromEither : (A -> B) -> Either A B -> B
fromEither f (left a) = f a
fromEither _ (right b) = b

split : (A -> B) -> (A -> C) -> A -> Tuple B C
split f g a = (f a , g a)

swap : Tuple A B -> Tuple B A
swap = split snd fst

dupe : A -> Tuple A A
dupe a = (a , a)

uncurry : (A -> B -> C) -> Tuple A B -> C
uncurry f (a , b) = f a b

curry : (Tuple A B -> C) -> A -> B -> C
curry f a b = f (a , b)

apply : Tuple (A -> B) A -> B
apply = uncurry _$_

isJust : Maybe A -> Bool
isJust (just _) = true
isJust _ = false

IsJust : Maybe A -> Set
IsJust (just _) = Unit
IsJust _ = Void

isNothing : Maybe A -> Bool
isNothing (just _) = false
isNothing _ = true

fromJust : (x : Maybe A) {_ : IsJust x} -> A
fromJust (just a) = a

maybe : B -> (A -> B) -> Maybe A -> B
maybe b f nothing = b
maybe b f (just a) = f a

maybeToLeft : B -> Maybe A -> Either A B
maybeToLeft b = maybe (right b) left

maybeToRight : B -> Maybe A -> Either B A
maybeToRight b = mirror <<< maybeToLeft b

leftToMaybe : Either A B -> Maybe A
leftToMaybe = either just (const nothing)

rightToMaybe : Either A B -> Maybe B
rightToMaybe = leftToMaybe <<< mirror

ensure : (A -> Bool) -> A -> Maybe A
ensure p a = if p a then just a else nothing

pattern [_] x = x :: []

listrec : B -> (A -> List A -> B -> B) -> List A -> B
listrec b f [] = b
listrec b f (a :: as) = f a as (listrec b f as)

maybeToList : Maybe A -> List A
maybeToList nothing = []
maybeToList (just a) = a :: []

listToMaybe : List A -> Maybe A
listToMaybe [] = nothing
listToMaybe (a :: _) = just a

private
  postulate
    mapIO : (A -> B) -> IO A -> IO B
    pureIO : A -> IO A
    apIO : IO (A -> B) -> IO A -> IO B
    bindIO : IO A -> (A -> IO B) -> IO B

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
-- BooleanAlgebra
--------------------------------------------------------------------------------

record BooleanAlgebra (B : Set) : Set where
  infixr 2 _||_
  infixr 3 _&&_
  field
    ff : B
    tt : B
    not : B -> B
    _||_ : B -> B -> B
    _&&_ : B -> B -> B

open BooleanAlgebra {{...}} public

instance
  booleanAlgebraBool : BooleanAlgebra Bool
  booleanAlgebraBool .ff = false
  booleanAlgebraBool .tt = true
  booleanAlgebraBool .not = \ where
    false -> true
    true -> false
  booleanAlgebraBool ._||_ = \ where
    false b -> b
    true _ -> true
  booleanAlgebraBool ._&&_ = \ where
    false _ -> false
    true b -> b

  booleanAlgebraFunction : {{_ : BooleanAlgebra B}} -> BooleanAlgebra (A -> B)
  booleanAlgebraFunction .ff = const ff
  booleanAlgebraFunction .tt = const tt
  booleanAlgebraFunction .not f = not <<< f
  booleanAlgebraFunction ._||_ f g a = f a || g a
  booleanAlgebraFunction ._&&_ f g a = f a && g a

--------------------------------------------------------------------------------
-- Eq
--------------------------------------------------------------------------------

record Eq (A : Set) : Set where
  infix 4 _==_
  field _==_ : A -> A -> Bool

  infix 4 _/=_
  _/=_ : A -> A -> Bool
  a /= a' = if a == a' then false else true

open Eq {{...}} public

instance
  eqVoid : Eq Void
  eqVoid ._==_ = \ ()

  eqUnit : Eq Unit
  eqUnit ._==_ unit unit = true

  eqBool : Eq Bool
  eqBool ._==_ = \ where
    true true -> true
    false false -> false
    _ _ -> false

  eqNat : Eq Nat
  eqNat ._==_ = Agda.Builtin.Nat._==_

  eqInt : Eq Int
  eqInt ._==_ = \ where
    (pos m) (pos n) -> m == n
    (negsuc m) (negsuc n) -> m == n
    _ _ -> false

  eqFloat : Eq Float
  eqFloat ._==_ = Agda.Builtin.Float.primFloatNumericalEquality

  eqChar : Eq Char
  eqChar ._==_ = Agda.Builtin.Char.primCharEquality

  eqString : Eq String
  eqString ._==_ = Agda.Builtin.String.primStringEquality

  eqEither : {{_ : Eq A}} {{_ : Eq B}} -> Eq (Either A B)
  eqEither ._==_ = \ where
    (left a) (left a') -> a == a'
    (right b) (right b') -> b == b'
    _ _ -> false

  eqTuple : {{_ : Eq A}} {{_ : Eq B}} -> Eq (Tuple A B)
  eqTuple ._==_ (a , b) (a' , b') = (a == a') && (b == b')

  eqMaybe : {{_ : Eq A}} -> Eq (Maybe A)
  eqMaybe ._==_ = \ where
    nothing nothing -> true
    (just a) (just a') -> a == a'
    _ _ -> false

  eqList : {{_ : Eq A}} -> Eq (List A)
  eqList ._==_ = \ where
    [] [] -> true
    (a :: as) (a' :: as') -> a == a' && as == as'
    _ _ -> false

  eqIdentity : {{_ : Eq A}} -> Eq (Identity A)
  eqIdentity ._==_ (identity: a) (identity: a') = a == a'

  eqConst : {{_ : Eq A}} -> Eq (Const A B)
  eqConst ._==_ (const: a) (const: a') = a == a'

--------------------------------------------------------------------------------
-- Ord
--------------------------------------------------------------------------------

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (A : Set) : Set where
  infixl 4 _<_
  field
    overlap {{super}} : Eq A
    _<_ : A -> A -> Bool

  compare : A -> A -> Ordering
  compare a a' = if a < a' then LT else if a == a' then EQ else GT

  infixl 4 _≤_
  _≤_ : A -> A -> Bool
  a ≤ a' = if a < a' then true else if a == a' then true else false

  infixl 4 _>_
  _>_ : A -> A -> Bool
  _>_ = flip _<_

  infixl 4 _≥_
  _≥_ : A -> A -> Bool
  _≥_ = flip _≤_

  min : A -> A -> A
  min x y = if x < y then x else y

  max : A -> A -> A
  max x y = if x < y then y else x

  comparing : (B -> A) -> B -> B -> Ordering
  comparing p b b' = compare (p b) (p b')

open Ord {{...}} public

instance
  ordVoid : Ord Void
  ordVoid ._<_ = \ ()

  ordUnit : Ord Unit
  ordUnit ._<_ unit unit = false

  ordBool : Ord Bool
  ordBool ._<_ = \ where
    false true -> true
    _ _ -> false

  ordNat : Ord Nat
  ordNat ._<_ = Agda.Builtin.Nat._<_

  ordInt : Ord Int
  ordInt ._<_ = \ where
    (pos m) (pos n) -> m < n
    (negsuc m) (negsuc n) -> m > n
    (negsuc _) (pos _) -> true
    (pos _) (negsuc _) -> false

  ordFloat : Ord Float
  ordFloat ._<_ = Agda.Builtin.Float.primFloatNumericalLess

  ordChar : Ord Char
  ordChar ._<_ c c' = ord c < ord c'

  ordList : {{_ : Ord A}} -> Ord (List A)
  ordList ._<_ = \ where
    (a :: as) (a' :: as') -> a < a' || (a == a' && as < as')
    [] [] -> true
    _ _ -> false

  ordString : Ord String
  ordString ._<_ s s' with unpack s | unpack s'
  ... | (c :: cs) | (c' :: cs') = c < c' || (c == c' && cs < cs')
  ... | _ | _ = false

  ordTuple : {{_ : Ord A}} {{_ : Ord B}} -> Ord (Tuple A B)
  ordTuple ._<_ (a , b) (a' , b') = a < a' || (a == a' && b < b')

  ordMaybe : {{_ : Ord A}} -> Ord (Maybe A)
  ordMaybe ._<_ = \ where
    _ nothing -> false
    nothing _ -> true
    (just a) (just a') -> a < a'

  ordIdentity : {{_ : Ord A}} -> Ord (Identity A)
  ordIdentity ._<_ (identity: a) (identity: a') = a < a'

  ordConst : {{_ : Ord A}} -> Ord (Const A B)
  ordConst ._<_ (const: a) (const: a') = a < a'

--------------------------------------------------------------------------------
-- Enum
--------------------------------------------------------------------------------

record Enum (A : Set) : Set where
  field
    {{super}} : Ord A
    next : A -> Maybe A
    prev : A -> Maybe A

open Enum {{...}} public

{-# TERMINATING #-}
range : {{_ : Enum A}} -> A -> A -> List A
range a a' = a :: maybe [] (flip range a') (
  case compare a a' of \ where
    EQ -> nothing
    LT -> next a
    GT -> prev a
  )

instance
  enumNat : Enum Nat
  enumNat .next n = just (suc n)
  enumNat .prev 0 = nothing
  enumNat .prev (suc n) = just n

  enumInt : Enum Int
  enumInt .next (pos n) = just (pos (suc n))
  enumInt .next (negsuc 0) = just (pos 0)
  enumInt .next (negsuc (suc n)) = just (negsuc n)
  enumInt .prev (pos 0) = just (negsuc 0)
  enumInt .prev (pos (suc n)) = just (pos n)
  enumInt .prev (negsuc n) = just (negsuc (suc n))

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
      fromNat = \ n -> n
    }

  fromNatInt : FromNat Int
  fromNatInt = record {
      Constraint = const Unit;
      fromNat = \ n -> pos n
    }

  fromNegInt : FromNeg Int
  fromNegInt = record {
      Constraint = const Unit;
      fromNeg = \ n -> neg n
    }

  fromNegFloat : FromNeg Float
  fromNegFloat = record {
      Constraint = const Unit;
      fromNeg = \ x -> Agda.Builtin.Float.primFloatNegate (natToFloat x)
    }

--------------------------------------------------------------------------------
-- Nonzero
--------------------------------------------------------------------------------

record NonzeroConstraint (A : Set) : Set where
  field IsNonzero : A -> Set

open NonzeroConstraint {{...}} public

data Nonzero (A : Set) : Set where
  nonzero: : {{_ : NonzeroConstraint A}}
    (a : A) {_ : IsNonzero a} -> Nonzero A

getNonzero : Nonzero A -> A
getNonzero (nonzero: a) = a

instance
  nonzeroConstraintNat : NonzeroConstraint Nat
  nonzeroConstraintNat .IsNonzero 0 = Void
  nonzeroConstraintNat .IsNonzero _ = Unit

  nonzeroConstraintInt : NonzeroConstraint Int
  nonzeroConstraintInt .IsNonzero (pos 0) = Void
  nonzeroConstraintInt .IsNonzero _ = Unit

  fromNatNonzeroNat : FromNat (Nonzero Nat)
  fromNatNonzeroNat = record {
      Constraint = IsNonzero;
      fromNat = \ { 0 -> undefined; (suc n) -> nonzero: (suc n) }
    }

  fromNatNonzeroInt : FromNat (Nonzero Int)
  fromNatNonzeroInt = record {
      Constraint = IsNonzero;
      fromNat = \ n -> nonzero: (pos n) {believeMe}
    }

  fromNegNonzeroInt : FromNeg (Nonzero Int)
  fromNegNonzeroInt = record {
      Constraint = IsNonzero;
      fromNeg = \ n -> nonzero: (neg n) {believeMe}
    }

--------------------------------------------------------------------------------
-- Arithmetic operations
--------------------------------------------------------------------------------

record Addition (A : Set) : Set where
  infixl 6 _+_
  field _+_ : A -> A -> A

open Addition {{...}} public

record Multiplication (A : Set) : Set where
  infixl 7 _*_
  field _*_ : A -> A -> A

open Multiplication {{...}} public

record Power (A : Set) : Set where
  infixr 10 _^_
  field _^_ : A -> Nat -> A

open Power {{...}} public

record Exponentiation (A : Set) : Set where
  infixr 8 _**_
  field _**_ : A -> A -> A

open Exponentiation {{...}} public

record Negation (A : Set) : Set where
  field -_ : A -> A

open Negation {{...}} public

record Subtraction (A : Set) : Set where
  infixl 6 _-_
  field _-_ : A -> A -> A

open Subtraction {{...}} public

record Division (A : Set) : Set where
  infixl 7 _/_
  field
    DivisionConstraint : A -> Set
    _/_ : (a a' : A) {_ : DivisionConstraint a'} -> A

open Division {{...}} public

record Modulus (A : Set) : Set where
  infixl 7 _%_
  field
    ModulusConstraint : A -> Set
    _%_ : (a a' : A) {{_ : ModulusConstraint a'}} -> A

open Modulus {{...}} public

record Signed (A : Set) : Set where
  field
    abs : A -> A
    signum : A -> A
open Signed {{...}} public

instance
  additionSet : Addition Set
  additionSet ._+_ = Either

  multiplicationSet : Multiplication Set
  multiplicationSet ._*_ = Tuple

  powerSet : Power Set
  powerSet ._^_ A = \ where
    0 -> Unit
    1 -> A
    (suc n) -> A ^ n * A

  additionNat : Addition Nat
  additionNat ._+_ = Agda.Builtin.Nat._+_

  multiplicationNat : Multiplication Nat
  multiplicationNat ._*_ = Agda.Builtin.Nat._*_

  powerNat : Power Nat
  powerNat ._^_ a = \ where
    0 -> 1
    1 -> a
    (suc n) -> a ^ n * a

  exponentiationNat : Exponentiation Nat
  exponentiationNat ._**_ = _^_

  subtractionNat : Subtraction Nat
  subtractionNat ._-_ = Agda.Builtin.Nat._-_

  divisionNat : Division Nat
  divisionNat .DivisionConstraint = IsNonzero
  divisionNat ._/_ m (suc n) = divAux 0 n m n
    where divAux = Agda.Builtin.Nat.div-helper

  modulusNat : Modulus Nat
  modulusNat .ModulusConstraint = IsNonzero
  modulusNat ._%_ m (suc n) = modAux 0 n m n
    where modAux = Agda.Builtin.Nat.mod-helper

  additionInt : Addition Int
  additionInt ._+_ = add
    where
      sub' : Nat -> Nat -> Int
      sub' m 0 = pos m
      sub' 0 (suc n) = negsuc n
      sub' (suc m) (suc n) = sub' m n

      add : Int -> Int -> Int
      add (negsuc m) (negsuc n) = negsuc (suc (m + n))
      add (negsuc m) (pos n) = sub' n (suc m)
      add (pos m) (negsuc n) = sub' m (suc n)
      add (pos m) (pos n) = pos (m + n)

  multiplicationInt : Multiplication Int
  multiplicationInt ._*_ = \ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> neg (n * suc m)
    (negsuc n) (pos m) -> neg (suc n * m)

  powerInt : Power Int
  powerInt ._^_ a = \ where
    0 -> 1
    1 -> a
    (suc n) -> a ^ n * a

  negationInt : Negation Int
  negationInt .-_ = \ where
    (pos 0) -> pos 0
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)

  subtractionInt : Subtraction Int
  subtractionInt ._-_ m n = m + (- n)

  divisionInt : Division Int
  divisionInt .DivisionConstraint = IsNonzero
  divisionInt ._/_ x y with x | y
  ... | pos m | pos (suc n) = pos (m / suc n)
  ... | negsuc m | pos (suc n) = neg (suc m / suc n)
  ... | pos m | negsuc n = neg (m / suc n)
  ... | negsuc m | negsuc n = pos (suc m / suc n)
  ... | _ | _ = error "quot {{divisionInt}} undefined"

  modulusInt : Modulus Int
  modulusInt .ModulusConstraint = IsNonzero
  modulusInt ._%_ x y with x | y
  ... | pos m | pos (suc n) = pos (m % suc n)
  ... | negsuc m | pos (suc n) = neg (suc m % suc n)
  ... | pos m | negsuc n = pos (m % suc n)
  ... | negsuc m | negsuc n = neg (suc m % suc n)
  ... | _ | _ = error "_%_ {{modulusInt}} undefined"

  signedInt : Signed Int
  signedInt .abs = \ where
    (pos n) -> pos n
    (negsuc n) -> pos (suc n)
  signedInt .signum = \ where
    (pos 0) -> pos 0
    (pos (suc _)) -> pos 1
    (negsuc _) -> negsuc 0

  additionFloat : Addition Float
  additionFloat ._+_ = Agda.Builtin.Float.primFloatPlus

  multiplicationFloat : Multiplication Float
  multiplicationFloat ._*_ = Agda.Builtin.Float.primFloatTimes

  powerFloat : Power Float
  powerFloat ._^_ a = \ where
    0 -> 1.0
    1 -> a
    (suc n) -> a ^ n * a

  exponentiationFloat : Exponentiation Float
  exponentiationFloat ._**_ x y = exp (y * log x)

  negationFloat : Negation Float
  negationFloat .-_ = Agda.Builtin.Float.primFloatNegate

  subtractionFloat : Subtraction Float
  subtractionFloat ._-_ = Agda.Builtin.Float.primFloatMinus

  nonzeroConstraintFloat : NonzeroConstraint Float
  nonzeroConstraintFloat .IsNonzero 0.0 = Void
  nonzeroConstraintFloat .IsNonzero _ = Unit

  divisionFloat : Division Float
  divisionFloat .DivisionConstraint = const Unit
  divisionFloat ._/_ x y = Agda.Builtin.Float.primFloatDiv x y

  signedFloat : Signed Float
  signedFloat .abs x = if x < 0.0 then - x else x
  signedFloat .signum x with compare x 0.0
  ... | EQ = 0.0
  ... | LT = -1.0
  ... | GT = 1.0

  additionFunction : {{_ : Addition B}} -> Addition (A -> B)
  additionFunction ._+_ f g x = f x + g x

  multiplicationFunction : {{_ : Multiplication B}} -> Multiplication (A -> B)
  multiplicationFunction ._*_ f g x = f x * g x

  negationFunction : {{_ : Negation B}} -> Negation (A -> B)
  negationFunction .-_ f x = - (f x)

  subtractionFunction : {{_ : Subtraction B}} -> Subtraction (A -> B)
  subtractionFunction ._-_ f g x = f x - g x

  powerFunction : Power (A -> A)
  powerFunction ._^_ f = \ where
    0 -> id
    1 -> f
    (suc n) -> f ^ n <<< f

--------------------------------------------------------------------------------
-- Semigroup
--------------------------------------------------------------------------------

record Semigroup (A : Set) : Set where
  infixr 5 _<>_
  field _<>_ : A -> A -> A

open Semigroup {{...}} public

-- For additive semigroups, monoids, etc.
record Sum (A : Set) : Set where
  constructor sum:
  field getSum : A

open Sum public

-- For multiplicative semigroups, monoids, etc.
record Product (A : Set) : Set where
  constructor product:
  field getProduct : A

open Product public

-- For dual semigroups, orders, etc.
record Dual (A : Set) : Set where
  constructor dual:
  field getDual : A

open Dual public

-- Semigroup where x <> y = x
record First (A : Set) : Set where
  constructor first:
  field getFirst : A

open First public

-- Semigroup where x <> y = y
record Last (A : Set) : Set where
  constructor last:
  field getLast : A

open Last public

-- For semigroups, monoids, etc. where x <> y = min x y
record Min (A : Set) : Set where
  constructor min:
  field getMin : A

open Min public

-- For Semigroups, monoids, etc. where x <> y = max x y
record Max (A : Set) : Set where
  constructor max:
  field getMax : A

open Max public

-- Bool semigroup where x <> y = x || y.
record Any : Set where
  constructor any:
  field getAny : Bool

open Any public

-- Bool semigroup where x <> y = x && y.
record All : Set where
  constructor all:
  field getAll : Bool

open All public

instance
  semigroupDual : {{_ : Semigroup A}} -> Semigroup (Dual A)
  semigroupDual ._<>_ (dual: a) (dual: a') = dual: (a' <> a)

  semigroupFirst : Semigroup (First A)
  semigroupFirst ._<>_ a _ = a

  semigroupLast : Semigroup (Last A)
  semigroupLast ._<>_ _ a = a

  semigroupMin : {{_ : Ord A}} -> Semigroup (Min A)
  semigroupMin ._<>_ (min: a) (min: a') = min: (min a a')

  semigroupMax : {{_ : Ord A}} -> Semigroup (Max A)
  semigroupMax ._<>_ (max: a) (max: a') = max: (max a a')

  semigroupAny : Semigroup Any
  semigroupAny ._<>_ (any: b) (any: b') = any: (b || b')

  semigroupAll : Semigroup All
  semigroupAll ._<>_ (all: b) (all: b') = all: (b && b')

  semigroupVoid : Semigroup Void
  semigroupVoid ._<>_ = \ ()

  semigroupUnit : Semigroup Unit
  semigroupUnit ._<>_ unit unit = unit

  semigroupSumNat : Semigroup (Sum Nat)
  semigroupSumNat ._<>_ (sum: m) (sum: n) = sum: (m + n)

  semigroupProductNat : Semigroup (Product Nat)
  semigroupProductNat ._<>_ (product: x) (product: y) = product: (x * y)

  semigroupSumInt : Semigroup (Sum Int)
  semigroupSumInt ._<>_ (sum: m) (sum: n) = sum: (m + n)

  semigroupProductInt : Semigroup (Product Int)
  semigroupProductInt ._<>_ (product: x) (product: y) = product: (x * y)

  semigroupString : Semigroup String
  semigroupString ._<>_ = Agda.Builtin.String.primStringAppend

  semigroupFunction : {{_ : Semigroup B}} -> Semigroup (A -> B)
  semigroupFunction ._<>_ f g = \ a -> f a <> g a

  semigroupEither : {{_ : Semigroup A}} {{_ : Semigroup B}}
    -> Semigroup (Either A B)
  semigroupEither ._<>_ (left _) b = b
  semigroupEither ._<>_ a _ = a

  semigroupTuple : {{_ : Semigroup A}} {{_ : Semigroup B}}
    -> Semigroup (Tuple A B)
  semigroupTuple ._<>_ (a , b) (a' , b') = (a <> a' , b <> b')

  semigroupMaybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  semigroupMaybe ._<>_ = \ where
    nothing m -> m
    m nothing -> m
    (just a) (just a') -> just (a <> a')

  semigroupList : Semigroup (List A)
  semigroupList ._<>_ as as' = listrec as' (\ x _ xs -> x :: xs) as

  semigroupIO : {{_ : Semigroup A}} -> Semigroup (IO A)
  semigroupIO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

  semigroupIdentity : {{_ : Semigroup A}} -> Semigroup (Identity A)
  semigroupIdentity ._<>_ (identity: a) (identity: a') =
    identity: (a <> a')

  semigroupConst : {{_ : Semigroup A}} -> Semigroup (Const A B)
  semigroupConst ._<>_ (const: a) (const: a') = const: (a <> a')

  semigroupEndo : Semigroup (Endo A)
  semigroupEndo ._<>_ g f = endo: (appEndo g <<< appEndo f)

--------------------------------------------------------------------------------
-- Monoid
--------------------------------------------------------------------------------

record Monoid (A : Set) : Set where
  field
    overlap {{super}} : Semigroup A
    neutral : A

  when : Bool -> A -> A
  when true a = a
  when false _ = neutral

  unless : Bool -> A -> A
  unless true _ = neutral
  unless false a = a

open Monoid {{...}} public

instance
  monoidDual : {{_ : Monoid A}} -> Monoid (Dual A)
  monoidDual .neutral = dual: neutral

  monoidFirst : {{_ : Monoid A}} -> Monoid (First A)
  monoidFirst .neutral = first: neutral

  monoidLast : {{_ : Monoid A}} -> Monoid (Last A)
  monoidLast .neutral = last: neutral

  monoidUnit : Monoid Unit
  monoidUnit .neutral = unit

  monoidAll : Monoid All
  monoidAll .neutral = all: true

  monoidAny : Monoid Any
  monoidAny .neutral = any: false

  monoidSumNat : Monoid (Sum Nat)
  monoidSumNat .neutral = sum: 0

  monoidProductNat : Monoid (Product Nat)
  monoidProductNat .neutral = product: (suc 0)

  monoidSumInt : Monoid (Sum Int)
  monoidSumInt .neutral = sum: 0

  monoidProductInt : Monoid (Product Int)
  monoidProductInt .neutral = product: 1

  monoidString : Monoid String
  monoidString .neutral = ""

  monoidFunction : {{_ : Monoid B}} -> Monoid (A -> B)
  monoidFunction .neutral = const neutral

  monoidEndo : Monoid (Endo A)
  monoidEndo .neutral = endo: id

  monoidMaybe : {{_ : Semigroup A}} -> Monoid (Maybe A)
  monoidMaybe .neutral = nothing

  monoidList : Monoid (List A)
  monoidList .neutral = []

  monoidIO : {{_ : Monoid A}} -> Monoid (IO A)
  monoidIO .neutral = pureIO neutral

  monoidIdentity : {{_ : Monoid A}} -> Monoid (Identity A)
  monoidIdentity .neutral = identity: neutral

  monoidConst : {{_ : Monoid A}} -> Monoid (Const A B)
  monoidConst .neutral = const: neutral

--------------------------------------------------------------------------------
-- IsBuildable, Buildable
--------------------------------------------------------------------------------

record IsBuildable (S A : Set) : Set where
  field
    {{monoid}} : Monoid S
    singleton : A -> S

  infixr 5 _++_
  _++_ : S -> S -> S
  _++_ = _<>_

  nil : S
  nil = neutral

  cons : A -> S -> S
  cons a s = singleton a ++ s

  snoc : S -> A -> S
  snoc s a = s ++ singleton a

  fromList : List A -> S
  fromList [] = nil
  fromList (a :: as) = cons a (fromList as)

  fromMaybe : Maybe A -> S
  fromMaybe nothing = nil
  fromMaybe (just a) = singleton a

  replicate : Nat -> A -> S
  replicate n a = applyN (cons a) n nil

open IsBuildable {{...}} public

Buildable : (Set -> Set) -> Set
Buildable F = ∀ {A} -> IsBuildable (F A) A

{-# TERMINATING #-}
unfoldr : {{_ : IsBuildable S A}} -> (B -> Maybe (Tuple A B)) -> B -> S
unfoldr f b with f b
... | nothing = nil
... | (just (a , b')) = cons a (unfoldr f b')

{-# TERMINATING #-}
unfoldl : {{_ : IsBuildable S A}} -> (B -> Maybe (Tuple B A)) -> B -> S
unfoldl f b with f b
... | nothing = nil
... | (just (b' , a)) = snoc (unfoldl f b') a

instance
  buildableList : Buildable List
  buildableList .singleton = _:: []

  isBuildableStringChar : IsBuildable String Char
  isBuildableStringChar .singleton = pack <<< singleton

--------------------------------------------------------------------------------
-- Functor, Contravariant, Bifunctor, Profunctor
--------------------------------------------------------------------------------

infixr 0 _~>_
_~>_ : (F G : Set -> Set) -> Set
F ~> G  = ∀ {A} -> F A -> G A

record Functor (F : Set -> Set) : Set where
  field map : (A -> B) -> F A -> F B

  infixl 4 _<$>_
  _<$>_ : (A -> B) -> F A -> F B
  _<$>_ = map

  infixl 4 _<$_
  _<$_ : B -> F A -> F B
  _<$_ = map <<< const

  infixl 4 _$>_
  _$>_ : F A -> B -> F B
  _$>_ = flip _<$_

  void : F A -> F Unit
  void = map (const unit)

open Functor {{...}} public

record Contravariant (F : Set -> Set) : Set where
  field contramap : (A -> B) -> F B -> F A

  phantom : {{_ : Functor F}} -> F A -> F B
  phantom x = contramap (const unit) $ map (const unit) x

open Contravariant {{...}} public

record Bifunctor (P : Set -> Set -> Set) : Set where
  field bimap : (A -> B) -> (C -> D) -> P A C -> P B D

  first : (A -> B) -> P A C -> P B C
  first f = bimap f id

  second : (B -> C) -> P A B -> P A C
  second g = bimap id g

open Bifunctor {{...}} public

record Profunctor (P : Set -> Set -> Set) : Set where
  field dimap : (A -> B) -> (C -> D) -> P B C -> P A D

  lmap : (A -> B) -> P B C -> P A C
  lmap f = dimap f id

  rmap : (B -> C) -> P A B -> P A C
  rmap f = dimap id f

open Profunctor {{...}} public

instance
  profunctorFunction : Profunctor Function
  profunctorFunction .dimap f g h = g <<< h <<< f

  bifunctorEither : Bifunctor Either
  bifunctorEither .bimap f g = either (left <<< f) (right <<< g)

  functorEither : Functor (Either A)
  functorEither .map = second

  bifunctorTuple : Bifunctor Tuple
  bifunctorTuple .bimap f g = split (f <<< fst) (g <<< snd)

  functorTuple : Functor (Tuple A)
  functorTuple .map = second

  functorMaybe : Functor Maybe
  functorMaybe .map f = \ where
    nothing -> nothing
    (just a) -> just (f a)

  functorList : Functor List
  functorList .map f = listrec [] \ a _ bs -> f a :: bs

  functorIO : Functor IO
  functorIO .map = mapIO

  functorIdentity : Functor Identity
  functorIdentity .map f = identity: <<< f <<< runIdentity

  bifunctorConst : Bifunctor Const
  bifunctorConst .bimap f g = const: <<< f <<< getConst

  functorConst : Functor (Const A)
  functorConst .map = second

  contravariantConst : Contravariant (Const A)
  contravariantConst .contramap f = const: <<< getConst

  functorSum : Functor Sum
  functorSum .map f = sum: <<< f <<< getSum

  functorProduct : Functor Product
  functorProduct .map f = product: <<< f <<< getProduct

  functorDual : Functor Dual
  functorDual .map f = dual: <<< f <<< getDual

  functorFirst : Functor First
  functorFirst .map f = first: <<< f <<< getFirst

  functorLast : Functor Last
  functorLast .map f = last: <<< f <<< getLast

  functorMin : Functor Min
  functorMin .map f = min: <<< f <<< getMin

  functorMax : Functor Max
  functorMax .map f = max: <<< f <<< getMax

--------------------------------------------------------------------------------
-- Applicative
--------------------------------------------------------------------------------

record Applicative (F : Set -> Set) : Set where
  infixl 4 _<*>_
  field
    overlap {{super}} : Functor F
    _<*>_ : F (A -> B) -> F A -> F B
    pure : A -> F A

  infixl 4 _*>_
  _*>_ : F A -> F B -> F B
  a *> b = (| (flip const) a b |)

  infixl 4 _<*_
  _<*_ : F A -> F B -> F A
  a <* b = (| const a b |)

open Applicative {{...}} public

instance
  applicativeEither : Applicative (Either A)
  applicativeEither .pure = right
  applicativeEither ._<*>_ = \ where
    (left a) _ -> left a
    (right f) -> map f

  applicativeMaybe : Applicative Maybe
  applicativeMaybe .pure = just
  applicativeMaybe ._<*>_ = \ where
    (just f) -> map f
    nothing _ -> nothing

  applicativeList : Applicative List
  applicativeList .pure = singleton
  applicativeList ._<*>_ = \ where
    [] _ -> []
    _ [] -> []
    (f :: fs) (x :: xs) -> f x :: (fs <*> xs)

  applicativeIO : Applicative IO
  applicativeIO .pure = pureIO
  applicativeIO ._<*>_ = apIO

  applicativeIdentity : Applicative Identity
  applicativeIdentity .pure = identity:
  applicativeIdentity ._<*>_ = map <<< runIdentity

  applicativeConst : {{_ : Monoid A}} -> Applicative (Const A)
  applicativeConst .pure _ = const: neutral
  applicativeConst ._<*>_ (const: f) (const: a) = const: (f <> a)

  applicativeSum : Applicative Sum
  applicativeSum .pure = sum:
  applicativeSum ._<*>_ (sum: f) (sum: x) = sum: (f x)

  applicativeProduct : Applicative Product
  applicativeProduct .pure = product:
  applicativeProduct ._<*>_ (product: f) (product: x) = product: (f x)

  applicativeDual : Applicative Dual
  applicativeDual .pure = dual:
  applicativeDual ._<*>_ (dual: f) (dual: x) = dual: (f x)

  applicativeFirst : Applicative First
  applicativeFirst .pure = first:
  applicativeFirst ._<*>_ (first: f) (first: x) = first: (f x)

  applicativeLast : Applicative Last
  applicativeLast .pure = last:
  applicativeLast ._<*>_ (last: f) (last: x) = last: (f x)

  applicativeMin : Applicative Min
  applicativeMin .pure = min:
  applicativeMin ._<*>_ (min: f) (min: x) = min: (f x)

  applicativeMax : Applicative Max
  applicativeMax .pure = max:
  applicativeMax ._<*>_ (max: f) (max: x) = max: (f x)

--------------------------------------------------------------------------------
-- Alternative
--------------------------------------------------------------------------------

record Alternative (F : Set -> Set) : Set where
  infixl 3 _<|>_
  field
    overlap {{super}} : Applicative F
    _<|>_ : F A -> F A -> F A
    empty : F A

open Alternative {{...}} public

module _ {{_ : Alternative F}} where

  guard : Bool -> F Unit
  guard true = pure unit
  guard false = empty

instance
  alternativeMaybe : Alternative Maybe
  alternativeMaybe .empty = nothing
  alternativeMaybe ._<|>_ = \ where
    nothing r -> r
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
    _>>=_ : M A -> (A -> M B) -> M B

  join : M (M A) -> M A
  join = _>>= id

  infixl 1 _>>_
  _>>_ : M A -> M B -> M B
  _>>_ = _*>_

open Monad {{...}} public

return : ∀ {A M} {{_ : Monad M}} -> A -> M A
return = pure

instance
  monadEither : Monad (Either A)
  monadEither ._>>=_ = \ where
    (left a) k -> left a
    (right x) k -> k x

  monadMaybe : Monad Maybe
  monadMaybe ._>>=_ = \ where
    nothing k -> nothing
    (just x) k -> k x

  monadList : Monad List
  monadList ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x ++ (xs >>= k)

  monadIO : Monad IO
  monadIO ._>>=_ = bindIO

  monadIdentity : Monad Identity
  monadIdentity ._>>=_ (identity: x) k = k x

  monadSum : Monad Sum
  monadSum ._>>=_ (sum: x) k = k x

  monadProduct : Monad Product
  monadProduct ._>>=_ (product: x) k = k x

  monadDual : Monad Dual
  monadDual ._>>=_ (dual: x) k = k x

  monadFirst : Monad First
  monadFirst ._>>=_ (first: x) k = k x

  monadLast : Monad Last
  monadLast ._>>=_ (last: x) k = k x

  monadMin : Monad Min
  monadMin ._>>=_ (min: x) k = k x

  monadMax : Monad Max
  monadMax ._>>=_ (max: x) k = k x

--------------------------------------------------------------------------------
-- IsNonempty, Nonempty
--------------------------------------------------------------------------------

record NonemptyConstraint (S : Set) : Set where
  field IsNonempty : S -> Set

open NonemptyConstraint {{...}} public

abstract
  Nonempty : Set -> Set
  Nonempty S = S

  nonempty : {{_ : NonemptyConstraint S}} (s : S) {_ : IsNonempty s}
    -> Nonempty S
  nonempty s = s

  getNonempty : Nonempty S -> S
  getNonempty s = s

instance
  nonemptyConstraintString : NonemptyConstraint String
  nonemptyConstraintString .IsNonempty "" = Void
  nonemptyConstraintString .IsNonempty _ = Unit

  nonemptyConstraintList : NonemptyConstraint (List A)
  nonemptyConstraintList .IsNonempty [] = Void
  nonemptyConstraintList .IsNonempty _ = Unit

--------------------------------------------------------------------------------
-- IsFoldable, Foldable
--------------------------------------------------------------------------------

record IsFoldable (S A : Set) : Set where
  field foldMap : {{_ : Monoid B}} -> (A -> B) -> S -> B

  foldMap1 : {{_ : Semigroup B}} -> (A -> B) -> Nonempty S -> B
  foldMap1 f s = fromJust (foldMap (just <<< f) (getNonempty s)) {believeMe}

  fold : {{_ : Monoid A}} -> S -> A
  fold = foldMap id

  fold1 : {{_ : Semigroup A}} -> Nonempty S -> A
  fold1 s = fromJust (foldMap just (getNonempty s)) {believeMe}

  foldr : (A -> B -> B) -> B -> S -> B
  foldr f b as = appEndo (foldMap (endo: <<< f) as) b

  foldr1 : (A -> A -> A) -> Nonempty S -> A
  foldr1 f s = fromJust (foldr g nothing (getNonempty s)) {believeMe}
    where
      g : A -> Maybe A -> Maybe A
      g a nothing = just a
      g a (just a') = just (f a a')

  foldl : (B -> A -> B) -> B -> S -> B
  foldl f b as =
    (appEndo <<< getDual) (foldMap (dual: <<< endo: <<< flip f) as) b

  foldl1 : (A -> A -> A) -> Nonempty S -> A
  foldl1 f s = fromJust (foldl g nothing (getNonempty s)) {believeMe}
    where
      g : Maybe A -> A -> Maybe A
      g nothing a = just a
      g (just a) a' = just (f a a')

  foldrM : {{_ : Monad M}} -> (A -> B -> M B) -> B -> S -> M B
  foldrM f b as = let g k a b' = f a b' >>= k in
    foldl g return as b

  foldlM : {{_ : Monad M}} -> (B -> A -> M B) -> B -> S -> M B
  foldlM f b as = let g a k b' = f b' a >>= k in
    foldr g return as b

  toList : S -> List A
  toList = foldMap [_]

  count : S -> Nat
  count = getSum <<< foldMap (const $ sum: (suc 0))

  all : (A -> Bool) -> S -> Bool
  all p = getAll <<< foldMap (all: <<< p)

  any : (A -> Bool) -> S -> Bool
  any p = getAny <<< foldMap (any: <<< p)

  null : S -> Bool
  null = not <<< any (const true)

  sum : {{ _ : Monoid (Sum A)}} -> S -> A
  sum = getSum <<< foldMap sum:

  product : {{ _ : Monoid (Product A)}} -> S -> A
  product = getProduct <<< foldMap product:

  find : (A -> Bool) -> S -> Maybe A
  find p = map getFirst <<< foldMap (map first: <<< ensure p)

  module _ {{_ : Eq A}} where

    elem : A -> S -> Bool
    elem = any <<< _==_

    notElem : A -> S -> Bool
    notElem a s = not (elem a s)

  module _ {{_ : Ord A}} where

    minimum : Nonempty S -> A
    minimum = foldr1 min

    maximum : Nonempty S -> A
    maximum = foldr1 max

  module _ {{_ : Applicative F}} where

    traverse! : (A -> F B) -> S -> F Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : S -> (A -> F B) -> F Unit
    for! = flip traverse!

  module _ {{_ : BooleanAlgebra A}} where

    or : S -> A
    or = foldr _||_ ff

    and : S -> A
    and = foldr _&&_ tt

open IsFoldable {{...}} public

sequence! : {{_ : Applicative F}} {{_ : IsFoldable S (F A)}} -> S -> F Unit
sequence! = traverse! id

Foldable : (Set -> Set) -> Set
Foldable F = ∀ {A} -> IsFoldable (F A) A

instance
  isFoldableNatUnit : IsFoldable Nat Unit
  isFoldableNatUnit .foldMap b 0 = neutral
  isFoldableNatUnit .foldMap b (suc n) = b unit <> foldMap b n

  foldableEither : Foldable (Either A)
  foldableEither .foldMap _ (left _) = neutral
  foldableEither .foldMap f (right x) = f x

  foldableTuple : Foldable (Tuple A)
  foldableTuple .foldMap f (_ , x) = f x

  foldableMaybe : Foldable Maybe
  foldableMaybe .foldMap = maybe neutral

  foldableList : Foldable List
  foldableList .foldMap f = listrec neutral \ x _ y -> f x <> y

  isFoldableStringChar : IsFoldable String Char
  isFoldableStringChar .foldMap f = foldMap f <<< unpack

--------------------------------------------------------------------------------
-- Traversable
--------------------------------------------------------------------------------

private
  record StateL (S A : Set) : Set where
    constructor stateL:
    field runStateL : S -> Tuple S A

  open StateL

  record StateR (S A : Set) : Set where
    constructor stateR:
    field runStateR : S -> Tuple S A

  open StateR

  instance
    functorStateL : Functor (StateL S)
    functorStateL .map f (stateL: t) = stateL: \ s0 ->
      let (s1 , x) = t s0 in (s1 , f x)

    functorStateR : Functor (StateR S)
    functorStateR .map f (stateR: t) = stateR: \ s0 ->
      let (s1 , x) = t s0 in (s1 , f x)

    applicativeStateL : Applicative (StateL S)
    applicativeStateL .pure x = stateL: \ s -> (s , x)
    applicativeStateL ._<*>_ (stateL: f) (stateL: t) = stateL: \ s0 ->
      let (s1 , f') = f s0; (s2 , x) = t s1 in (s2 , f' x)

    applicativeStateR : Applicative (StateR S)
    applicativeStateR .pure x = stateR: \ s -> (s , x)
    applicativeStateR ._<*>_ (stateR: f) (stateR: t) = stateR: \ s0 ->
      let (s1 , x) = t s0; (s2 , f') = f s1 in (s2 , f' x)

record Traversable (T : Set -> Set) : Set where
  field
    {{superFunctor}} : Functor T
    {{superFoldable}} : Foldable T
    traverse : {{_ : Applicative F}} -> (A -> F B) -> T A -> F (T B)

  sequence : {{_ : Applicative F}} -> T (F A) -> F (T A)
  sequence = traverse id

  for : {{_ : Applicative F}} -> T A -> (A -> F B) -> F (T B)
  for = flip traverse

  mapAccumL : (A -> B -> Tuple A C) -> A -> T B -> Tuple A (T C)
  mapAccumL f a xs = runStateL (traverse (stateL: <<< flip f) xs) a

  mapAccumR : (A -> B -> Tuple A C) -> A -> T B -> Tuple A (T C)
  mapAccumR f a xs = runStateR (traverse (stateR: <<< flip f) xs) a

  scanl : {{_ : Buildable T}} -> (B -> A -> B) -> B -> T A -> T B
  scanl f b0 xs = uncurry (flip snoc) (mapAccumL (\ b a -> (f b a , b)) b0 xs)

  scanr : {{_ : Buildable T}} -> (A -> B -> B) -> B -> T A -> T B
  scanr f b0 xs = uncurry cons (mapAccumR (\ b a -> (f a b , b)) b0 xs)

open Traversable {{...}} public

instance
  traversableEither : Traversable (Either A)
  traversableEither .traverse f = \ where
    (left a) -> pure (left a)
    (right x) -> map right (f x)

  traversableTuple : Traversable (Tuple A)
  traversableTuple .traverse f (a , x) = map (a ,_) (f x)

  traversableMaybe : Traversable Maybe
  traversableMaybe .traverse f = \ where
    nothing -> pure nothing
    (just x) -> map just (f x)

  traversableList : Traversable List
  traversableList .traverse f = listrec (pure []) \ where
    x _ ys -> (| _::_ (f x) ys |)

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

record Show (A : Set) : Set where
  field show : A -> String

  print : A -> IO Unit
  print a = putStrLn (show a)

open Show {{...}} public

instance
  showVoid : Show Void
  showVoid .show ()

  showUnit : Show Unit
  showUnit .show unit = "unit"

  showBool : Show Bool
  showBool .show true = "true"
  showBool .show false = "false"

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

  showTuple : {{_ : Show A}} {{_ : Show B}} -> Show (Tuple A B)
  showTuple .show (a , b) = "(" ++ show a ++ " , " ++ show b ++ ")"

  showEither : {{_ : Show A}} {{_ : Show B}} -> Show (Either A B)
  showEither .show = \ where
    (left a) -> "(left " ++ show a ++ ")"
    (right b) -> "(right " ++ show b ++ ")"

  showMaybe : {{_ : Show A}} -> Show (Maybe A)
  showMaybe .show = \ where
    (just a) -> "(just " ++ show a ++ ")"
    nothing -> "nothing"

  showList : {{_ : Show A}} -> Show (List A)
  showList .show [] = "[]"
  showList .show as = "[ " ++ show' as ++ " ]"
    where
      show' : {{_ : Show A}} -> List A -> String
      show' [] = ""
      show' (a :: []) = show a
      show' (a :: as) = show a ++ " , " ++ show' as

  showIdentity : {{_ : Show A}} -> Show (Identity A)
  showIdentity .show (identity: a) = "(identity: " ++ show a ++ ")"

  showConst : {{_ : Show A}} -> Show (Const A B)
  showConst .show (const: a) = "(const: " ++ show a ++ ")"

  showSum : {{_ : Show A}} -> Show (Sum A)
  showSum .show (sum: a) = "(sum: " ++ show a ++ ")"

  showProduct : {{_ : Show A}} -> Show (Product A)
  showProduct .show (product: a) = "(product: " ++ show a ++ ")"

  showDual : {{_ : Show A}} -> Show (Dual A)
  showDual .show (dual: a) = "(dual: " ++ show a ++ ")"

  showFirst : {{_ : Show A}} -> Show (First A)
  showFirst .show (first: a) = "(first: " ++ show a ++ ")"

  showLast : {{_ : Show A}} -> Show (Last A)
  showLast .show (last: a) = "(last: " ++ show a ++ ")"

  showMin : {{_ : Show A}} -> Show (Min A)
  showMin .show (min: a) = "(min: " ++ show a ++ ")"

  showMax : {{_ : Show A}} -> Show (Max A)
  showMax .show (max: a) = "(max: " ++ show a ++ ")"

  showAny : Show Any
  showAny .show (any: a) = "(any: " ++ show a ++ ")"

  showAll : Show All
  showAll .show (all: a) = "(all: " ++ show a ++ ")"
