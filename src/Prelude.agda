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

open import Agda.Builtin.Sigma public
  using (Σ; _,_; fst; snd)

Tuple : Set -> Set -> Set
Tuple A B = Σ A (λ _ -> B)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

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

id : A -> A
id a = a

const : A -> B -> A
const a _ = a

flip : (A -> B -> C) -> B -> A -> C
flip f b a = f a b

infixr 0 _$_
_$_ : (A -> B) -> A -> B
_$_ = id

case_of_ : A -> (A -> B) -> B
case_of_ = flip _$_

infixr 9 _∘_
_∘_ : (B -> C) -> (A -> B) -> A -> C
g ∘ f = λ a -> g (f a)

infixr 10 if_then_else_
if_then_else_ : Bool -> A -> A -> A
if true then a else _ = a
if false then _ else a = a

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ zero = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

applyN : (A -> A) -> Nat -> A -> A
applyN f n a = natrec a (const f) n

monus : Nat -> Nat -> Nat
monus = Agda.Builtin.Nat._-_

pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

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

isNothing : Maybe A -> Bool
isNothing (just _) = false
isNothing _ = true

maybe : B -> (A -> B) -> Maybe A -> B
maybe b f nothing = b
maybe b f (just a) = f a

fromMaybe : A -> Maybe A -> A
fromMaybe = flip maybe id

maybeToLeft : B -> Maybe A -> Either A B
maybeToLeft b = maybe (right b) left

maybeToRight : B -> Maybe A -> Either B A
maybeToRight b = mirror ∘ maybeToLeft b

leftToMaybe : Either A B -> Maybe A
leftToMaybe = either just (const nothing)

rightToMaybe : Either A B -> Maybe B
rightToMaybe = leftToMaybe ∘ mirror

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
  booleanAlgebraBool .not = λ where
    false -> true
    true -> false
  booleanAlgebraBool ._||_ = λ where
    false b -> b
    true _ -> true
  booleanAlgebraBool ._&&_ = λ where
    false _ -> false
    true b -> b

  booleanAlgebraFunction : {{_ : BooleanAlgebra B}} -> BooleanAlgebra (A -> B)
  booleanAlgebraFunction .ff = const ff
  booleanAlgebraFunction .tt = const tt
  booleanAlgebraFunction .not f = not ∘ f
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
  eqVoid ._==_ = λ ()

  eqUnit : Eq Unit
  eqUnit ._==_ unit unit = true

  eqBool : Eq Bool
  eqBool ._==_ = λ where
    true true -> true
    false false -> false
    _ _ -> false

  eqNat : Eq Nat
  eqNat ._==_ = Agda.Builtin.Nat._==_

  eqInt : Eq Int
  eqInt ._==_ = λ where
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
  eqEither ._==_ = λ where
    (left a) (left a') -> a == a'
    (right b) (right b') -> b == b'
    _ _ -> false

  eqTuple : {{_ : Eq A}} {{_ : Eq B}} -> Eq (Tuple A B)
  eqTuple ._==_ (a , b) (a' , b') = (a == a') && (b == b')

  eqMaybe : {{_ : Eq A}} -> Eq (Maybe A)
  eqMaybe ._==_ = λ where
    nothing nothing -> true
    (just a) (just a') -> a == a'
    _ _ -> false

  eqList : {{_ : Eq A}} -> Eq (List A)
  eqList ._==_ = λ where
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
  ordVoid ._<_ = λ ()

  ordUnit : Ord Unit
  ordUnit ._<_ unit unit = false

  ordBool : Ord Bool
  ordBool ._<_ = λ where
    false true -> true
    _ _ -> false

  ordNat : Ord Nat
  ordNat ._<_ = Agda.Builtin.Nat._<_

  ordInt : Ord Int
  ordInt ._<_ = λ where
    (pos m) (pos n) -> m < n
    (negsuc m) (negsuc n) -> m > n
    (negsuc _) (pos _) -> true
    (pos _) (negsuc _) -> false

  ordFloat : Ord Float
  ordFloat ._<_ = Agda.Builtin.Float.primFloatNumericalLess

  ordChar : Ord Char
  ordChar ._<_ c c' = ord c < ord c'

  ordList : {{_ : Ord A}} -> Ord (List A)
  ordList ._<_ = λ where
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
  ordMaybe ._<_ = λ where
    _ nothing -> false
    nothing _ -> true
    (just a) (just a') -> a < a'

  ordIdentity : {{_ : Ord A}} -> Ord (Identity A)
  ordIdentity ._<_ (identity: a) (identity: a') = a < a'

  ordConst : {{_ : Ord A}} -> Ord (Const A B)
  ordConst ._<_ (const: a) (const: a') = a < a'

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
  fromNatInt : FromNat Int
  fromNatInt = record {
      Constraint = const Unit;
      fromNat = λ n -> pos n
    }

  fromNegInt : FromNeg Int
  fromNegInt = record {
      Constraint = const Unit;
      fromNeg = λ where
        zero -> pos zero
        (suc n) -> negsuc n
    }

--------------------------------------------------------------------------------
-- Overloadable arithmetic operators
--------------------------------------------------------------------------------

record Plus (A : Set) : Set where
  infixl 6 _+_
  field _+_ : A -> A -> A

open Plus {{...}} public

record Times (A : Set) : Set where
  infixl 7 _*_
  field _*_ : A -> A -> A

open Times {{...}} public

record Negative (A R : Set) : Set where
  field -_ : A -> R

open Negative {{...}} public

record Minus (A R : Set) : Set where
  infixl 6 _-_
  field _-_ : A -> A -> R

open Minus {{...}} public

record Division (A R : Set) : Set where
  infixl 7 _/_
  field _/_ : A -> A -> R

open Division {{...}} public

instance
  plusFloat : Plus Float
  plusFloat ._+_ = Agda.Builtin.Float.primFloatPlus

  timesFloat : Times Float
  timesFloat ._*_ = Agda.Builtin.Float.primFloatTimes

  negativeFloat : Negative Float Float
  negativeFloat .-_ = Agda.Builtin.Float.primFloatNegate

  minusFloat : Minus Float Float
  minusFloat ._-_ = Agda.Builtin.Float.primFloatMinus

  divisionFloat : Division Float Float
  divisionFloat ._/_ = Agda.Builtin.Float.primFloatDiv

  plusNat : Plus Nat
  plusNat ._+_ = Agda.Builtin.Nat._+_

  timesNat : Times Nat
  timesNat ._*_ = Agda.Builtin.Nat._*_

  negativeNatInt : Negative Nat Int
  negativeNatInt .-_ = λ { zero -> pos zero;  (suc n) -> negsuc n }

  minusNatInt : Minus Nat Int
  minusNatInt ._-_ = λ where
    m zero -> pos m
    zero (suc n) -> negsuc n
    (suc m) (suc n) -> m - n

  divisionNatFloat : Division Nat Float
  divisionNatFloat ._/_ m n = (natToFloat m) / (natToFloat n)

  plusInt : Plus Int
  plusInt ._+_ = λ where
    (negsuc m) (negsuc n) -> negsuc (suc (m + n))
    (negsuc m) (pos n) -> n - suc m
    (pos m) (negsuc n) -> m - suc n
    (pos m) (pos n) -> pos (m + n)

  timesInt : Times Int
  timesInt ._*_ = λ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> - (n * suc m)
    (negsuc n) (pos m) -> - (suc n * m)

  negativeInt : Negative Int Int
  negativeInt .-_ = λ where
    (pos zero) -> pos zero
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)

  minusInt : Minus Int Int
  minusInt ._-_ m n = m + (- n)

  divisionIntFloat : Division Int Float
  divisionIntFloat ._/_ = λ where
    (pos m) (pos n) -> m / n
    (pos m) (negsuc n) -> - (m / suc n)
    (negsuc m) (pos n) -> - (suc m / n)
    (negsuc m) (negsuc n) -> (suc m) / (suc n)

  plusFunction : {{_ : Plus B}} -> Plus (A -> B)
  plusFunction ._+_ f g x = f x + g x

  timesFunction : {{_ : Times B}} -> Times (A -> B)
  timesFunction ._*_ f g x = f x * g x

  negativeFunction : {{_ : Negative B R}} -> Negative (A -> B) (A -> R)
  negativeFunction .-_ f x = - (f x)

  minusFunction : {{_ : Minus B R}} -> Minus (A -> B) (A -> R)
  minusFunction ._-_ f g x = f x - g x

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
  semigroupVoid ._<>_ = λ ()

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
  semigroupFunction ._<>_ f g = λ a -> f a <> g a

  semigroupEither : {{_ : Semigroup A}} {{_ : Semigroup B}}
    -> Semigroup (Either A B)
  semigroupEither ._<>_ (left _) b = b
  semigroupEither ._<>_ a _ = a

  semigroupTuple : {{_ : Semigroup A}} {{_ : Semigroup B}}
    -> Semigroup (Tuple A B)
  semigroupTuple ._<>_ (a , b) (a' , b') = (a <> a' , b <> b')

  semigroupMaybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  semigroupMaybe ._<>_ = λ where
    nothing m -> m
    m nothing -> m
    (just a) (just a') -> just (a <> a')

  semigroupList : Semigroup (List A)
  semigroupList ._<>_ as as' = listrec as' (λ x _ xs -> x :: xs) as

  semigroupIO : {{_ : Semigroup A}} -> Semigroup (IO A)
  semigroupIO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

  semigroupIdentity : {{_ : Semigroup A}} -> Semigroup (Identity A)
  semigroupIdentity ._<>_ (identity: a) (identity: a') =
    identity: (a <> a')

  semigroupConst : {{_ : Semigroup A}} -> Semigroup (Const A B)
  semigroupConst ._<>_ (const: a) (const: a') = const: (a <> a')

  semigroupEndo : Semigroup (Endo A)
  semigroupEndo ._<>_ g f = endo: (appEndo g ∘ appEndo f)

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
  monoidSumNat .neutral = sum: zero

  monoidProductNat : Monoid (Product Nat)
  monoidProductNat .neutral = product: (suc zero)

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

open IsBuildable {{...}} public

Buildable : (Set -> Set) -> Set
Buildable F = ∀ {A} -> IsBuildable (F A) A

instance
  buildableList : Buildable List
  buildableList .singleton = _:: []

  isBuildableStringChar : IsBuildable String Char
  isBuildableStringChar .singleton = pack ∘ singleton

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
  _<$_ = map ∘ const

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
  profunctorFunction .dimap f g h = g ∘ h ∘ f

  bifunctorEither : Bifunctor Either
  bifunctorEither .bimap f g = either (left ∘ f) (right ∘ g)

  functorEither : Functor (Either A)
  functorEither .map = second

  bifunctorTuple : Bifunctor Tuple
  bifunctorTuple .bimap f g = split (f ∘ fst) (g ∘ snd)

  functorTuple : Functor (Tuple A)
  functorTuple .map = second

  functorMaybe : Functor Maybe
  functorMaybe .map f = λ where
    nothing -> nothing
    (just a) -> just (f a)

  functorList : Functor List
  functorList .map f = listrec [] λ a _ bs -> f a :: bs

  functorIO : Functor IO
  functorIO .map = mapIO

  functorIdentity : Functor Identity
  functorIdentity .map f = identity: ∘ f ∘ runIdentity

  bifunctorConst : Bifunctor Const
  bifunctorConst .bimap f g = const: ∘ f ∘ getConst

  functorConst : Functor (Const A)
  functorConst .map = second

  contravariantConst : Contravariant (Const A)
  contravariantConst .contramap f = const: ∘ getConst

  functorSum : Functor Sum
  functorSum .map f = sum: ∘ f ∘ getSum

  functorProduct : Functor Product
  functorProduct .map f = product: ∘ f ∘ getProduct

  functorDual : Functor Dual
  functorDual .map f = dual: ∘ f ∘ getDual

  functorFirst : Functor First
  functorFirst .map f = first: ∘ f ∘ getFirst

  functorLast : Functor Last
  functorLast .map f = last: ∘ f ∘ getLast

  functorMin : Functor Min
  functorMin .map f = min: ∘ f ∘ getMin

  functorMax : Functor Max
  functorMax .map f = max: ∘ f ∘ getMax

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

  map2 : (A -> B -> C) -> F A -> F B -> F C
  map2 f a b = (| f a b |)

open Applicative {{...}} public

instance
  applicativeEither : Applicative (Either A)
  applicativeEither .pure = right
  applicativeEither ._<*>_ = λ where
    (left a) _ -> left a
    (right f) -> map f

  applicativeMaybe : Applicative Maybe
  applicativeMaybe .pure = just
  applicativeMaybe ._<*>_ = λ where
    (just f) -> map f
    nothing _ -> nothing

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
  applicativeIdentity .pure = identity:
  applicativeIdentity ._<*>_ = map ∘ runIdentity

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

  {-# NON_TERMINATING #-}
  many1 many : F A -> F (List A)
  many1 a = (| _::_ a (many a) |)
  many a = many1 a <|> pure []

  optional : F A -> F (Maybe A)
  optional a = (| just a | nothing |)

  eitherA : F A -> F B -> F (Either A B)
  eitherA a b = (| left a | right b |)

instance
  alternativeMaybe : Alternative Maybe
  alternativeMaybe .empty = nothing
  alternativeMaybe ._<|>_ = λ where
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

  return : A -> M A
  return = pure

  join : M (M A) -> M A
  join = _>>= id

  infixl 1 _>>_
  _>>_ : M A -> M B -> M B
  _>>_ = _*>_

open Monad {{...}} public

instance
  monadEither : Monad (Either A)
  monadEither ._>>=_ = λ where
    (left a) k -> left a
    (right x) k -> k x

  monadMaybe : Monad Maybe
  monadMaybe ._>>=_ = λ where
    nothing k -> nothing
    (just x) k -> k x

  monadList : Monad List
  monadList ._>>=_ = λ where
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
-- IsFoldable, Foldable
--------------------------------------------------------------------------------

record IsFoldable (S A : Set) : Set where
  field foldMap : {{_ : Monoid B}} -> (A -> B) -> S -> B

  foldMap1 : {{_ : Semigroup B}} -> (A -> B) -> S -> Maybe B
  foldMap1 f = foldMap (just ∘ f)

  fold : {{_ : Monoid A}} -> S -> A
  fold = foldMap id

  fold1 : {{_ : Semigroup A}} -> S -> Maybe A
  fold1 = foldMap just

  foldr : (A -> B -> B) -> B -> S -> B
  foldr f b as = appEndo (foldMap (endo: ∘ f) as) b

  foldr1 : (A -> A -> A) -> S -> Maybe A
  foldr1 f = flip foldr nothing λ where
    a nothing -> just a
    a (just a') -> just (f a a')

  foldl : (B -> A -> B) -> B -> S -> B
  foldl f b as =
    (appEndo ∘ getDual) (foldMap (dual: ∘ endo: ∘ flip f) as) b

  foldl1 : (A -> A -> A) -> S -> Maybe A
  foldl1 f = flip foldl nothing λ where
    nothing a -> just a
    (just a) a' -> just (f a a')

  foldrM : {{_ : Monad M}} -> (A -> B -> M B) -> B -> S -> M B
  foldrM f b as = let g k a b' = f a b' >>= k in
    foldl g return as b

  foldlM : {{_ : Monad M}} -> (B -> A -> M B) -> B -> S -> M B
  foldlM f b as = let g a k b' = f b' a >>= k in
    foldr g return as b

  count : S -> Int
  count = getSum ∘ foldMap (const $ sum: 1)

  all : (A -> Bool) -> S -> Bool
  all p = getAll ∘ foldMap (all: ∘ p)

  any : (A -> Bool) -> S -> Bool
  any p = getAny ∘ foldMap (any: ∘ p)

  null : S -> Bool
  null = not ∘ any (const true)

  sum : {{ _ : Monoid (Sum A)}} -> S -> A
  sum = getSum ∘ foldMap sum:

  product : {{ _ : Monoid (Product A)}} -> S -> A
  product = getProduct ∘ foldMap product:

  find : (A -> Bool) -> S -> Maybe A
  find p = map getFirst ∘ foldMap (map first: ∘ ensure p)

  module _ {{_ : Eq A}} where

    elem : A -> S -> Bool
    elem = any ∘ _==_

    notElem : A -> S -> Bool
    notElem a s = not (elem a s)

  module _ {{_ : Ord A}} where

    minimum : S -> Maybe A
    minimum = foldr1 min

    maximum : S -> Maybe A
    maximum = foldr1 max

  module _ {{_ : Applicative F}} where

    traverse! : (A -> F B) -> S -> F Unit
    traverse! f = foldr (_*>_ ∘ f) (pure unit)

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
  isFoldableNatUnit .foldMap b zero = neutral
  isFoldableNatUnit .foldMap b (suc n) = b unit <> foldMap b n

  foldableEither : Foldable (Either A)
  foldableEither .foldMap _ (left _) = neutral
  foldableEither .foldMap f (right x) = f x

  foldableTuple : Foldable (Tuple A)
  foldableTuple .foldMap f (_ , x) = f x

  foldableMaybe : Foldable Maybe
  foldableMaybe .foldMap = maybe neutral

  foldableList : Foldable List
  foldableList .foldMap f = listrec neutral λ x _ y -> f x <> y

  isFoldableStringChar : IsFoldable String Char
  isFoldableStringChar .foldMap f = foldMap f ∘ unpack

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
    functorStateL .map f (stateL: t) = stateL: λ s₀ ->
      let (s₁ , x) = t s₀ in (s₁ , f x)

    functorStateR : Functor (StateR S)
    functorStateR .map f (stateR: t) = stateR: λ s₀ ->
      let (s₁ , x) = t s₀ in (s₁ , f x)

    applicativeStateL : Applicative (StateL S)
    applicativeStateL .pure x = stateL: λ s -> (s , x)
    applicativeStateL ._<*>_ (stateL: f) (stateL: t) = stateL: λ s₀ ->
      let (s₁ , f') = f s₀; (s₂ , x) = t s₁ in (s₂ , f' x)

    applicativeStateR : Applicative (StateR S)
    applicativeStateR .pure x = stateR: λ s -> (s , x)
    applicativeStateR ._<*>_ (stateR: f) (stateR: t) = stateR: λ s₀ ->
      let (s₁ , x) = t s₀; (s₂ , f') = f s₁ in (s₂ , f' x)

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
  mapAccumL f a xs = runStateL (traverse (stateL: ∘ flip f) xs) a

  mapAccumR : (A -> B -> Tuple A C) -> A -> T B -> Tuple A (T C)
  mapAccumR f a xs = runStateR (traverse (stateR: ∘ flip f) xs) a

  scanl : (B -> A -> B) -> B -> T A -> T B
  scanl f b₀ xs = snd (mapAccumL (λ b a -> dupe (f b a)) b₀ xs)

  scanr : (A -> B -> B) -> B -> T A -> T B
  scanr f b₀ xs = snd (mapAccumR (λ b a -> dupe (f a b)) b₀ xs)

open Traversable {{...}} public

instance
  traversableEither : Traversable (Either A)
  traversableEither .traverse f = λ where
    (left a) -> pure (left a)
    (right x) -> map right (f x)

  traversableTuple : Traversable (Tuple A)
  traversableTuple .traverse f (a , x) = map (a ,_) (f x)

  traversableMaybe : Traversable Maybe
  traversableMaybe .traverse f = λ where
    nothing -> pure nothing
    (just x) -> map just (f x)

  traversableList : Traversable List
  traversableList .traverse f = listrec (pure []) λ where
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
  showEither .show = λ where
    (left a) -> "(left " ++ show a ++ ")"
    (right b) -> "(right " ++ show b ++ ")"

  showMaybe : {{_ : Show A}} -> Show (Maybe A)
  showMaybe .show = λ where
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
