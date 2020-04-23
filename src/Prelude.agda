{-# OPTIONS --type-in-type #-}

module Prelude where

private
  variable
    A B C D S : Set
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
  using (Nat; suc)

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
  renaming (Σ to Sigma)

Pair : Set -> Set -> Set
Pair A B = Sigma A (\ _ -> B)

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

record Id (A : Set) : Set where
  constructor toId
  field fromId : A

open Id public

record Const (A B : Set) : Set where
  constructor toConst
  field fromConst : A

open Const public

-- For additive semigroups, monoids, etc.
record Sum (A : Set) : Set where
  constructor toSum
  field fromSum : A

open Sum public

-- For multiplicative semigroups, monoids, etc.
record Product (A : Set) : Set where
  constructor toProduct
  field fromProduct : A

open Product public

-- For dual semigroups, orders, etc.
record Dual (A : Set) : Set where
  constructor toDual
  field fromDual : A

open Dual public

-- Semigroup where x <> y = x
record First (A : Set) : Set where
  constructor toFirst
  field fromFirst : A

open First public

-- Semigroup where x <> y = y
record Last (A : Set) : Set where
  constructor toLast
  field fromLast : A

open Last public

-- For semigroups, monoids, etc. where x <> y = min x y
record Min (A : Set) : Set where
  constructor toMin
  field fromMin : A

open Min public

-- For Semigroups, monoids, etc. where x <> y = max x y
record Max (A : Set) : Set where
  constructor toMax
  field fromMax : A

open Max public

-- Bool semigroup where x <> y = x && y.
record All : Set where
  constructor toAll
  field fromAll : Bool

open All public

-- Bool semigroup where x <> y = x || y.
record Any : Set where
  constructor toAny
  field fromAny : Bool

open Any public

-- Endofunctions
record Endo A : Set where
  constructor toEndo
  field fromEndo : A -> A

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

infixr 9 _<<<_
_<<<_ : (B -> C) -> (A -> B) -> A -> C
g <<< f = \ a -> g (f a)

infixr 9 _>>>_
_>>>_ : (A -> B) -> (B -> C) -> A -> C
_>>>_ = flip _<<<_

absurd : Void -> A
absurd ()

infixr 10 if_then_else_
if_then_else_ : Bool -> A -> A -> A
if true then a else _ = a
if false then _ else a = a

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ 0 = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

applyN : (A -> A) -> Nat -> A -> A
applyN f n a = natrec a (const f) n

monus : Nat -> Nat -> Nat
monus = Agda.Builtin.Nat._-_

pred : Nat -> Nat
pred 0 = 0
pred (suc n) = n

foldZ : (Nat -> A) -> (Nat -> A) -> Int -> A
foldZ f g (pos n) = f n
foldZ f g (negsuc n) = g n

neg : Nat -> Int
neg 0 = pos 0
neg (suc n) = negsuc n

Nonneg : Int -> Set
Nonneg (pos _) = Unit
Nonneg _ = Void

nonneg : (n : Int) {_ : Nonneg n} -> Nat
nonneg (pos n) = n

private sub : Nat -> Nat -> Int
sub m 0 = pos m
sub 0 (suc n) = negsuc n
sub (suc m) (suc n) = sub m n

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
either f g (left x) = f x
either f g (right y) = g y

mirror : Either A B -> Either B A
mirror = either right left

untag : Either A A -> A
untag = either id id

isLeft : Either A B -> Bool
isLeft (left _) = true
isLeft _ = false

isRight : Either A B -> Bool
isRight (left _) = false
isRight _ = true

fromLeft : A -> Either A B -> A
fromLeft x = either id (const x)

fromRight : B -> Either A B -> B
fromRight y = either (const y) id

fromEither : (A -> B) -> Either A B -> B
fromEither f = either f id

split : (A -> B) -> (A -> C) -> A -> Pair B C
split f g a = (f a , g a)

swap : Pair A B -> Pair B A
swap = split snd fst

dupe : A -> Pair A A
dupe = split id id

uncurry : (A -> B -> C) -> Pair A B -> C
uncurry f (a , b) = f a b

curry : (Pair A B -> C) -> A -> B -> C
curry f a b = f (a , b)

apply : Pair (A -> B) A -> B
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
maybeToRight b = mirror <<< maybeToLeft b

leftToMaybe : Either A B -> Maybe A
leftToMaybe = either just (const nothing)

rightToMaybe : Either A B -> Maybe B
rightToMaybe = leftToMaybe <<< mirror

ensure : (A -> Bool) -> A -> Maybe A
ensure p a = if p a then just a else nothing

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
{-# COMPILE GHC mapIO = \ _ _ f io -> fmap f io #-}
{-# COMPILE GHC pureIO = \ _ a -> pure a #-}
{-# COMPILE GHC apIO = \ _ _ f x -> f <*> x #-}
{-# COMPILE GHC bindIO = \ _ _ io f -> io >>= f #-}
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
  booleanAlgebraFunction ._||_ f g x = f x || g x
  booleanAlgebraFunction ._&&_ f g x = f x && g x

--------------------------------------------------------------------------------
-- Eq
--------------------------------------------------------------------------------

record Eq (A : Set) : Set where
  infix 4 _==_
  field _==_ : A -> A -> Bool

  infix 4 _/=_
  _/=_ : A -> A -> Bool
  x /= y = if x == y then false else true

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
    (left x) (left y) -> x == y
    (right x) (right y) -> x == y
    _ _ -> false

  eqPair : {{_ : Eq A}} {{_ : Eq B}} -> Eq (Pair A B)
  eqPair ._==_ (a , b) (c , d) = (a == c) && (b == d)

  eqMaybe : {{_ : Eq A}} -> Eq (Maybe A)
  eqMaybe ._==_ = \ where
    nothing nothing -> true
    (just x) (just y) -> x == y
    _ _ -> false

  eqList : {{_ : Eq A}} -> Eq (List A)
  eqList ._==_ = \ where
    [] [] -> true
    (x :: xs) (y :: ys) -> x == y && xs == ys
    _ _ -> false

  eqId : {{_ : Eq A}} -> Eq (Id A)
  eqId ._==_ x y = fromId x == fromId y

  eqConst : {{_ : Eq A}} -> Eq (Const A B)
  eqConst ._==_ x y = fromConst x == fromConst y

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
  compare x y = if x < y then LT else if x == y then EQ else GT

  infixl 4 _<=_
  _<=_ : A -> A -> Bool
  x <= y = if x < y then true else if x == y then true else false

  infixl 4 _>_
  _>_ : A -> A -> Bool
  _>_ = flip _<_

  infixl 4 _>=_
  _>=_ : A -> A -> Bool
  _>=_ = flip _<=_

  min : A -> A -> A
  min x y = if x < y then x else y

  max : A -> A -> A
  max x y = if x < y then y else x

  comparing : (B -> A) -> B -> B -> Ordering
  comparing p x y = compare (p x) (p y)

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
    (x :: xs) (y :: ys) -> x < y || (x == y && xs < ys)
    [] [] -> true
    _ _ -> false

  ordString : Ord String
  ordString ._<_ s s' with unpack s | unpack s'
  ... | (c :: cs) | (c' :: cs') = c < c' || (c == c' && cs < cs')
  ... | _ | _ = false

  ordPair : {{_ : Ord A}} {{_ : Ord B}} -> Ord (Pair A B)
  ordPair ._<_ (a , b) (a' , b') = a < a' || (a == a' && b < b')

  ordMaybe : {{_ : Ord A}} -> Ord (Maybe A)
  ordMaybe ._<_ = \ where
    _ nothing -> false
    nothing _ -> true
    (just a) (just a') -> a < a'

  ordId : {{_ : Ord A}} -> Ord (Id A)
  ordId ._<_ x y = fromId x < fromId y

  ordConst : {{_ : Ord A}} -> Ord (Const A B)
  ordConst ._<_ x y = fromConst x < fromConst y

--------------------------------------------------------------------------------
-- Semigroup
--------------------------------------------------------------------------------

record Semigroup (A : Set) : Set where
  infixr 5 _<>_
  field _<>_ : A -> A -> A

open Semigroup {{...}} public

infixr 6 _+_
_+_ : {{_ : Semigroup (Sum A)}} -> A -> A -> A
x + y = fromSum (toSum x <> toSum y)

infixr 7 _*_
_*_ : {{_ : Semigroup (Product A)}} -> A -> A -> A
x * y = fromProduct (toProduct x <> toProduct y)

instance
  semigroupDual : {{_ : Semigroup A}} -> Semigroup (Dual A)
  semigroupDual ._<>_ x y = toDual $ fromDual y <> fromDual x

  semigroupFirst : Semigroup (First A)
  semigroupFirst ._<>_ x y = x

  semigroupLast : Semigroup (Last A)
  semigroupLast ._<>_ x y = y

  semigroupVoid : Semigroup Void
  semigroupVoid ._<>_ = \ ()

  semigroupSumSet : Semigroup (Sum Set)
  semigroupSumSet ._<>_ A B = toSum $ Either (fromSum A) (fromSum B)

  semigroupProductSet : Semigroup (Product Set)
  semigroupProductSet ._<>_ A B =
    toProduct $ Pair (fromProduct A) (fromProduct B)

  semigroupUnit : Semigroup Unit
  semigroupUnit ._<>_ unit unit = unit

  semigroupAll : Semigroup All
  semigroupAll ._<>_ x y = toAll (fromAll x && fromAll y)

  semigroupAny : Semigroup Any
  semigroupAny ._<>_ x y = toAny (fromAny x || fromAny y)

  semigroupSumNat : Semigroup (Sum Nat)
  semigroupSumNat ._<>_ m n =
    toSum $ Agda.Builtin.Nat._+_ (fromSum m) (fromSum n)

  semigroupProductNat : Semigroup (Product Nat)
  semigroupProductNat ._<>_ m n =
    toProduct $ Agda.Builtin.Nat._*_ (fromProduct m) (fromProduct n)

  semigroupSumInt : Semigroup (Sum Int)
  semigroupSumInt ._<>_ x y with fromSum x | fromSum y
  ... | (negsuc m) | (negsuc n) = toSum $ negsuc (suc (m + n))
  ... | (negsuc m) | (pos n) = toSum $ sub n (suc m)
  ... | (pos m) | (negsuc n) = toSum $ sub m (suc n)
  ... | (pos m) | (pos n) = toSum $ pos (m + n)

  semigroupProductInt : Semigroup (Product Int)
  semigroupProductInt ._<>_ x y with fromProduct x | fromProduct y
  ... | (pos n) | (pos m) = toProduct $ pos (n * m)
  ... | (negsuc n) | (negsuc m) = toProduct $ pos (suc n * suc m)
  ... | (pos n) | (negsuc m) = toProduct $ neg (n * suc m)
  ... | (negsuc n) | (pos m) = toProduct $ neg (suc n * m)

  semigroupSumFloat : Semigroup (Sum Float)
  semigroupSumFloat ._<>_ x y =
    toSum $ Agda.Builtin.Float.primFloatPlus (fromSum x) (fromSum y)

  semigroupProductFloat : Semigroup (Product Float)
  semigroupProductFloat ._<>_ x y = toProduct $
    Agda.Builtin.Float.primFloatTimes (fromProduct x) (fromProduct y)

  semigroupString : Semigroup String
  semigroupString ._<>_ = Agda.Builtin.String.primStringAppend

  semigroupFunction : {{_ : Semigroup B}} -> Semigroup (A -> B)
  semigroupFunction ._<>_ f g = \ a -> f a <> g a

  semigroupFunctionSum : {{_ : Semigroup (Sum B)}} -> Semigroup $ Sum (A -> B)
  semigroupFunctionSum ._<>_ f g = toSum $ \ a -> fromSum f a + fromSum g a

  semigroupFunctionProduct : {{_ : Semigroup (Product B)}}
    -> Semigroup $ Product (A -> B)
  semigroupFunctionProduct ._<>_ f g =
    toProduct $ \ a -> fromProduct f a * fromProduct g a

  semigroupEndo : Semigroup (Endo A)
  semigroupEndo ._<>_ g f = toEndo (fromEndo g <<< fromEndo f)

  semigroupEither : {{_ : Semigroup A}} {{_ : Semigroup B}}
    -> Semigroup (Either A B)
  semigroupEither ._<>_ (left _) b = b
  semigroupEither ._<>_ a _ = a

  semigroupPair : {{_ : Semigroup A}} {{_ : Semigroup B}}
    -> Semigroup (Pair A B)
  semigroupPair ._<>_ (a , b) (a' , b') = (a <> a' , b <> b')

  semigroupMaybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  semigroupMaybe ._<>_ = \ where
    nothing m -> m
    m nothing -> m
    (just x) (just y) -> just (x <> y)

  semigroupList : Semigroup (List A)
  semigroupList ._<>_ xs ys = listrec ys (\ a _ as -> a :: as) xs

  semigroupIO : {{_ : Semigroup A}} -> Semigroup (IO A)
  semigroupIO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

  semigroupId : {{_ : Semigroup A}} -> Semigroup (Id A)
  semigroupId ._<>_ x y = toId $ fromId x <> fromId y

  semigroupConst : {{_ : Semigroup A}} -> Semigroup (Const A B)
  semigroupConst ._<>_ x y = toConst $ fromConst x <> fromConst y

--------------------------------------------------------------------------------
-- Monoid
--------------------------------------------------------------------------------

record Monoid (A : Set) : Set where
  field
    overlap {{super}} : Semigroup A
    mempty : A

  when : Bool -> A -> A
  when true x = x
  when false _ = mempty

  unless : Bool -> A -> A
  unless true _ = mempty
  unless false x = x

open Monoid {{...}} public

-- For additive monoids
zero : {{_ : Monoid (Sum A)}} -> A
zero = fromSum mempty

-- For multiplicative monoids
one : {{_ : Monoid (Product A)}} -> A
one = fromProduct mempty

infixr 8 _^_
_^_ : {{_ : Monoid (Product A)}} -> A -> Nat -> A
a ^ 0 = one
a ^ (suc n) = a * a ^ n

instance
  monoidDual : {{_ : Monoid A}} -> Monoid (Dual A)
  monoidDual .mempty = toDual mempty

  monoidFirst : {{_ : Monoid A}} -> Monoid (First A)
  monoidFirst .mempty = toFirst mempty

  monoidLast : {{_ : Monoid A}} -> Monoid (Last A)
  monoidLast .mempty = toLast mempty

  monoidSumSet : Monoid (Sum Set)
  monoidSumSet .mempty = toSum Void

  monoidProductSet : Monoid (Product Set)
  monoidProductSet .mempty = toProduct Unit

  monoidUnit : Monoid Unit
  monoidUnit .mempty = unit

  monoidAll : Monoid All
  monoidAll .mempty = toAll true

  monoidAny : Monoid Any
  monoidAny .mempty = toAny false

  monoidSumNat : Monoid (Sum Nat)
  monoidSumNat .mempty = toSum 0

  monoidProductNat : Monoid (Product Nat)
  monoidProductNat .mempty = toProduct 1

  monoidSumInt : Monoid (Sum Int)
  monoidSumInt .mempty = toSum (pos 0)

  monoidProductInt : Monoid (Product Int)
  monoidProductInt .mempty = toProduct (pos 1)

  monoidSumFloat : Monoid (Sum Float)
  monoidSumFloat .mempty = toSum 0.0

  monoidProductFloat : Monoid (Product Float)
  monoidProductFloat .mempty = toProduct 1.0

  monoidString : Monoid String
  monoidString .mempty = ""

  monoidFunction : {{_ : Monoid B}} -> Monoid (A -> B)
  monoidFunction .mempty = const mempty

  monoidFunctionSum : {{_ : Monoid (Sum B)}} -> Monoid $ Sum (A -> B)
  monoidFunctionSum .mempty = toSum (const zero)

  monoidFunctionProduct : {{_ : Monoid (Product B)}}
    -> Monoid $ Product (A -> B)
  monoidFunctionProduct .mempty = toProduct (const one)

  monoidEndo : Monoid (Endo A)
  monoidEndo .mempty = toEndo id

  monoidMaybe : {{_ : Semigroup A}} -> Monoid (Maybe A)
  monoidMaybe .mempty = nothing

  monoidList : Monoid (List A)
  monoidList .mempty = []

  monoidIO : {{_ : Monoid A}} -> Monoid (IO A)
  monoidIO .mempty = pureIO mempty

  monoidId : {{_ : Monoid A}} -> Monoid (Id A)
  monoidId .mempty = toId mempty

  monoidConst : {{_ : Monoid A}} -> Monoid (Const A B)
  monoidConst .mempty = toConst mempty

--------------------------------------------------------------------------------
-- Semiring
--------------------------------------------------------------------------------

record Semiring (A : Set) : Set where
  field
    {{monoidSum}} : Monoid (Sum A)
    {{monoidProduct}} : Monoid (Product A)
    Nonzero : A -> Set

open Semiring {{...}} public

instance
  semiringNat : Semiring Nat
  semiringNat .Nonzero 0 = Void
  semiringNat .Nonzero (suc _) = Unit

  semiringInt : Semiring Int
  semiringInt .Nonzero (pos 0) = Void
  semiringInt .Nonzero _ = Unit

  semiringFloat : Semiring Float
  semiringFloat .Nonzero x = if x == 0.0 then Void else Unit

--------------------------------------------------------------------------------
-- EuclideanSemiring
--------------------------------------------------------------------------------

record EuclideanSemiring (A : Set) : Set where
  field
    {{super}} : Semiring A
    degree : A -> Nat
    quot : (a b : A) {_ : Nonzero b} -> A
    mod : (a b : A) {_ : Nonzero b} -> A

open EuclideanSemiring {{...}} public

instance
  euclideanSemiringNat : EuclideanSemiring Nat
  euclideanSemiringNat .degree n = n
  euclideanSemiringNat .quot m 0 = 0 -- unreachable
  euclideanSemiringNat .quot m (suc n) = Agda.Builtin.Nat.div-helper 0 n m n
  euclideanSemiringNat .mod m 0 = 0 -- unreachable
  euclideanSemiringNat .mod m (suc n) = Agda.Builtin.Nat.mod-helper 0 n m n

--------------------------------------------------------------------------------
-- Ring
--------------------------------------------------------------------------------

record Ring (A : Set) : Set where
  infixr 6 _-_
  field
    overlap {{super}} : Semiring A
    -_ : A -> A
    _-_ : A -> A -> A

  abs : {{_ : Ord A}} -> A -> A
  abs a = if a < zero then - a else a

open Ring {{...}} public

instance
  ringInt : Ring Int
  ringInt .-_ = \ where
    (pos 0) -> pos 0
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)
  ringInt ._-_ n m = n + (- m)

  ringFloat : Ring Float
  ringFloat .-_ = Agda.Builtin.Float.primFloatNegate
  ringFloat ._-_ = Agda.Builtin.Float.primFloatMinus

--------------------------------------------------------------------------------
-- Field
--------------------------------------------------------------------------------

record Field (A : Set) : Set where
  infixr 7 _/_
  field
    overlap {{super}} : Ring A
    _/_ : (x y : A) -> {_ : Nonzero y} -> A

open Field {{...}} public

instance
  fieldFloat : Field Float
  fieldFloat ._/_ x y = Agda.Builtin.Float.primFloatDiv x y

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
  nil = mempty

  cons : A -> S -> S
  cons a s = singleton a ++ s

  snoc : S -> A -> S
  snoc s a = s ++ singleton a

open IsBuildable {{...}} public

Buildable : (Set -> Set) -> Set
Buildable F = forall {A} -> IsBuildable (F A) A

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
F ~> G  = forall {A} -> F A -> G A

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
  void = unit <$_

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
  bifunctorEither : Bifunctor Either
  bifunctorEither .bimap f g = either (left <<< f) (right <<< g)

  functorEither : Functor (Either A)
  functorEither .map = second

  bifunctorPair : Bifunctor Pair
  bifunctorPair .bimap f g = split (f <<< fst) (g <<< snd)

  functorPair : Functor (Pair A)
  functorPair .map = second

  functorMaybe : Functor Maybe
  functorMaybe .map f = \ where
    nothing -> nothing
    (just a) -> just (f a)

  functorList : Functor List
  functorList .map f = listrec [] \ a _ bs -> f a :: bs

  functorIO : Functor IO
  functorIO .map = mapIO

  functorId : Functor Id
  functorId .map f = toId <<< f <<< fromId

  bifunctorConst : Bifunctor Const
  bifunctorConst .bimap f g = toConst <<< f <<< fromConst

  functorConst : Functor (Const A)
  functorConst .map = second

  contravariantConst : Contravariant (Const A)
  contravariantConst .contramap f = toConst <<< fromConst

  functorSum : Functor Sum
  functorSum .map f = toSum <<< f <<< fromSum

  functorProduct : Functor Product
  functorProduct .map f = toProduct <<< f <<< fromProduct

  functorDual : Functor Dual
  functorDual .map f = toDual <<< f <<< fromDual

  functorFirst : Functor First
  functorFirst .map f = toFirst <<< f <<< fromFirst

  functorLast : Functor Last
  functorLast .map f = toLast <<< f <<< fromLast

  functorMin : Functor Min
  functorMin .map f = toMin <<< f <<< fromMin

  functorMax : Functor Max
  functorMax .map f = toMax <<< f <<< fromMax

  profunctorFunction : Profunctor Function
  profunctorFunction .dimap f g h = g <<< h <<< f

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
  map2 f x y = (| f x y |)

open Applicative {{...}} public

instance
  applicativeEither : Applicative (Either A)
  applicativeEither .pure = right
  applicativeEither ._<*>_ = \ where
    (left a) _ -> left a
    (right f) x -> map f x

  applicativeMaybe : Applicative Maybe
  applicativeMaybe .pure = just
  applicativeMaybe ._<*>_ = \ where
    (just f) m -> map f m
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

  applicativeId : Applicative Id
  applicativeId .pure = toId
  applicativeId ._<*>_ = map <<< fromId

  applicativeConst : {{_ : Monoid A}} -> Applicative (Const A)
  applicativeConst = \ where
    .pure x -> toConst mempty
    ._<*>_ f x -> toConst $ fromConst f <> fromConst x

  applicativeSum : Applicative Sum
  applicativeSum .pure = toSum
  applicativeSum ._<*>_ f x = toSum $ fromSum f (fromSum x)

  applicativeProduct : Applicative Product
  applicativeProduct .pure = toProduct
  applicativeProduct ._<*>_ f x = toProduct $ fromProduct f (fromProduct x)

  applicativeDual : Applicative Dual
  applicativeDual .pure = toDual
  applicativeDual ._<*>_ f x = toDual $ fromDual f (fromDual x)

  applicativeFirst : Applicative First
  applicativeFirst .pure = toFirst
  applicativeFirst ._<*>_ f x = toFirst $ fromFirst f (fromFirst x)

  applicativeLast : Applicative Last
  applicativeLast .pure = toLast
  applicativeLast ._<*>_ f x = toLast $ fromLast f (fromLast x)

  applicativeMin : Applicative Min
  applicativeMin .pure = toMin
  applicativeMin ._<*>_ f x = toMin $ fromMin f (fromMin x)

  applicativeMax : Applicative Max
  applicativeMax .pure = toMax
  applicativeMax ._<*>_ f x = toMax $ fromMax f (fromMax x)

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

  {-# NON_TERMINATING #-}
  many1 many : F A -> F (List A)
  many1 v = (| _::_ v (many v) |)
  many v = many1 v <|> pure []

  optional : F A -> F (Maybe A)
  optional v = just <$> v <|> pure nothing

instance
  alternativeMaybe : Alternative Maybe
  alternativeMaybe .empty = nothing
  alternativeMaybe ._<|>_ = \ where
    nothing r -> r
    l _ -> l

  alternativeList : Alternative List
  alternativeList .empty = mempty
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

  infixr 1 _=<<_
  _=<<_ : (A -> M B) -> M A -> M B
  _=<<_ = flip _>>=_

  join : M (M A) -> M A
  join = _=<<_ id

  infixl 1 _>>_
  _>>_ : M A -> M B -> M B
  _>>_ = _*>_

  infixr 1 _<<_
  _<<_ : M A -> M B -> M A
  _<<_ = _<*_

  infixr 1 _<=<_
  _<=<_ : (B -> M C) -> (A -> M B) -> A -> M C
  g <=< f = f >>> (_>>= g)

  infixr 1 _>=>_
  _>=>_ : (A -> M B) -> (B -> M C) -> A -> M C
  _>=>_ = flip _<=<_

open Monad {{...}} public

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

  monadId : Monad Id
  monadId ._>>=_ a k = k (fromId a)

  monadSum : Monad Sum
  monadSum ._>>=_ m k = k (fromSum m)

  monadProduct : Monad Product
  monadProduct ._>>=_ m k = k (fromProduct m)

  monadDual : Monad Dual
  monadDual ._>>=_ m k = k (fromDual m)

  monadFirst : Monad First
  monadFirst ._>>=_ m k = k (fromFirst m)

  monadLast : Monad Last
  monadLast ._>>=_ m k = k (fromLast m)

  monadMin : Monad Min
  monadMin ._>>=_ m k = k (fromMin m)

  monadMax : Monad Max
  monadMax ._>>=_ m k = k (fromMax m)

--------------------------------------------------------------------------------
-- IsFoldable, Foldable
--------------------------------------------------------------------------------

record IsFoldable (S A : Set) : Set where
  field foldMap : {{_ : Monoid B}} -> (A -> B) -> S -> B

  fold : {{_ : Monoid A}} -> S -> A
  fold = foldMap id

  foldr : (A -> B -> B) -> B -> S -> B
  foldr f b as = fromEndo (foldMap (toEndo <<< f) as) b

  foldl : (B -> A -> B) -> B -> S -> B
  foldl f b as =
    (fromEndo <<< fromDual) (foldMap (toDual <<< toEndo <<< flip f) as) b

  foldrM : {{_ : Monad M}} -> (A -> B -> M B) -> B -> S -> M B
  foldrM f b as = let g k a b' = f a b' >>= k in
    foldl g return as b

  foldlM : {{_ : Monad M}} -> (B -> A -> M B) -> B -> S -> M B
  foldlM f b as = let g a k b' = f b' a >>= k in
    foldr g return as b

  count : S -> Nat
  count = fromSum <<< foldMap (const $ toSum 1)

  all : (A -> Bool) -> S -> Bool
  all p = fromAll <<< foldMap (toAll <<< p)

  any : (A -> Bool) -> S -> Bool
  any p = fromAny <<< foldMap (toAny <<< p)

  null : S -> Bool
  null = not <<< any (const true)

  sum : {{ _ : Monoid (Sum A)}} -> S -> A
  sum = fromSum <<< foldMap toSum

  product : {{ _ : Monoid (Product A)}} -> S -> A
  product = fromProduct <<< foldMap toProduct

  module _ {{_ : Eq A}} where

    elem : A -> S -> Bool
    elem = any <<< _==_

    notElem : A -> S -> Bool
    notElem a s = not (elem a s)

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
Foldable F = forall {A} -> IsFoldable (F A) A

instance
  foldableEither : Foldable (Either A)
  foldableEither .foldMap _ (left _) = mempty
  foldableEither .foldMap f (right y) = f y

  foldablePair : Foldable (Pair A)
  foldablePair .foldMap f (_ , y) = f y

  foldableMaybe : Foldable Maybe
  foldableMaybe .foldMap = maybe mempty

  foldableList : Foldable List
  foldableList .foldMap f = listrec mempty \ a _ b -> f a <> b

  isFoldableStringChar : IsFoldable String Char
  isFoldableStringChar .foldMap f = foldMap f <<< unpack

--------------------------------------------------------------------------------
-- Traversable
--------------------------------------------------------------------------------

private
  record StateL (S A : Set) : Set where
    constructor toStateL
    field fromStateL : S -> Pair S A

  open StateL

  record StateR (S A : Set) : Set where
    constructor toStateR
    field fromStateR : S -> Pair S A

  open StateR

  instance
    functorStateL : Functor (StateL S)
    functorStateL .map f mk = toStateL $ \ s0 ->
      let (s1 , v) = fromStateL mk s0 in (s1 , f v)

    functorStateR : Functor (StateR S)
    functorStateR .map f mk = toStateR $ \ s0 ->
      let (s1 , v) = fromStateR mk s0 in (s1 , f v)

    applicativeStateL : Applicative (StateL S)
    applicativeStateL .pure x = toStateL $ \ s -> (s , x)
    applicativeStateL ._<*>_ kf kv = toStateL $ \ s0 ->
      let
        (s1 , f) = fromStateL kf s0
        (s2 , v) = fromStateL kv s1
      in
        (s2 , f v)

    applicativeStateR : Applicative (StateR S)
    applicativeStateR .pure x = toStateR $ \ s -> (s , x)
    applicativeStateR ._<*>_ kf kv = toStateR $ \ s0 ->
      let
        (s1 , v) = fromStateR kv s0
        (s2 , f) = fromStateR kf s1
      in
        (s2 , f v)

record Traversable (T : Set -> Set) : Set where
  field
    {{superFunctor}} : Functor T
    {{superFoldable}} : Foldable T
    traverse : {{_ : Applicative F}} -> (A -> F B) -> T A -> F (T B)

  sequence : {{_ : Applicative F}} -> T (F A) -> F (T A)
  sequence = traverse id

  for : {{_ : Applicative F}} -> T A -> (A -> F B) -> F (T B)
  for = flip traverse

  mapAccumL : (A -> B -> Pair A C) -> A -> T B -> Pair A (T C)
  mapAccumL f s t = fromStateL (traverse (toStateL <<< flip f) t) s

  mapAccumR : (A -> B -> Pair A C) -> A -> T B -> Pair A (T C)
  mapAccumR f s t = fromStateR (traverse (toStateR <<< flip f) t) s

  scanl : (B -> A -> B) -> B -> T A -> T B
  scanl f b0 xs = snd $
    mapAccumL (\ b a -> let b' = f b a in (b' , b')) b0 xs

  scanr : (A -> B -> B) -> B -> T A -> T B
  scanr f b0 xs = snd $
    mapAccumR (\ b a -> let b' = f a b in (b' , b')) b0 xs

open Traversable {{...}} public

instance
  traversableEither : Traversable (Either A)
  traversableEither .traverse f = \ where
    (left x) -> pure (left x)
    (right y) -> right <$> f y

  traversablePair : Traversable (Pair A)
  traversablePair .traverse f (x , y) = _,_ x <$> f y

  traversableMaybe : Traversable Maybe
  traversableMaybe .traverse f = \ where
    nothing -> pure nothing
    (just x) -> just <$> f x

  traversableList : Traversable List
  traversableList .traverse f = listrec (pure []) \ where
    x _ ys -> (| _::_ (f x) ys |)

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

record Show (A : Set) : Set where
  field show : A -> String

  print : A -> IO Unit
  print x = putStrLn (show x)

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

  showPair : {{_ : Show A}} {{_ : Show B}} -> Show (Pair A B)
  showPair .show (x , y) = "(" ++ show x ++ " , " ++ show y ++ ")"

  showEither : {{_ : Show A}} {{_ : Show B}} -> Show (Either A B)
  showEither .show = \ where
    (left x) -> "left " ++ show x
    (right y) -> "right " ++ show y

  showMaybe : {{_ : Show A}} -> Show (Maybe A)
  showMaybe .show = \ where
    (just x) -> "just " ++ show x
    nothing -> "nothing"

  showList : {{_ : Show A}} -> Show (List A)
  showList .show [] = "[]"
  showList .show as = "(" ++ show' as ++ ")"
    where
      show' : {{_ : Show A}} -> List A -> String
      show' [] = "[]"
      show' (x :: xs) = show x ++ " :: " ++ show' xs

  showChar : Show Char
  showChar .show = Agda.Builtin.String.primShowChar

  showString : Show String
  showString .show = Agda.Builtin.String.primShowString
