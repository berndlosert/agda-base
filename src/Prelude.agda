{-# OPTIONS --type-in-type #-}

module Prelude where

private
  variable
    A B C D : Set
    F G : Set -> Set

--------------------------------------------------------------------------------
-- For notational convenience
--------------------------------------------------------------------------------

record Add (A : Set) : Set where
  infixr 24 _+_
  field _+_ : A -> A -> A

open Add {{...}} public

record Negation (A : Set) : Set where
  field -_ : A -> A

open Negation {{...}} public

record Sub (A : Set) : Set where
  infixr 24 _-_
  field _-_ : A -> A -> A

open Sub {{...}} public

record Mul (A : Set) : Set where
  infixr 25 _*_
  field _*_ : A -> A -> A

open Mul {{...}} public

record Div (A : Set) : Set where
  infixr 25 _/_
  field
    Constraint : A -> Set
    _/_ : (x y : A) -> {_ : Constraint y} -> A

open Div {{...}} hiding (Constraint) public

record Mod (A : Set) : Set where
  infixr 25 _%_
  field
    Constraint : A -> Set
    _%_ : (x y : A) -> {_ : Constraint y} -> A

open Mod {{...}} hiding (Constraint) public

record Exp (A B C : Set) : Set where
  infixr 50 _^_
  field _^_ : A -> B -> C

open Exp {{...}} public

record Append (A B C : Set) : Set where
  infixr 25 _++_
  field _++_ : A -> B -> C

open Append {{...}} public

open import Agda.Builtin.FromNat public
  using (Number; fromNat)

open import Agda.Builtin.FromNeg public
  using (Negative; fromNeg)

open import Agda.Builtin.FromString public
  using (IsString; fromString)

--------------------------------------------------------------------------------
-- Basic types
--------------------------------------------------------------------------------

data Void : Set where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit; tt to unit)

open import Agda.Builtin.Bool public
  using (Bool; true; false)

open import Agda.Builtin.Nat public
  using (Nat; zero; suc)

open import Agda.Builtin.Int public
  using (Int; pos; negsuc)

open import Agda.Builtin.Float public
  using (Float)

open import Agda.Builtin.Char public
  using (Char)

open import Agda.Builtin.String public
  using (String)

--------------------------------------------------------------------------------
-- Basic type constructors
--------------------------------------------------------------------------------

infixr 4 _,_

Function : Set -> Set -> Set
Function A B = A -> B

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _===_)

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair public

instance
  mulPair : Mul Set
  mulPair ._*_ = Pair

{-# FOREIGN GHC type AgdaPair a b = (a, b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Prelude.AgdaPair ((,)) #-}

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

instance
  addEither : Add Set
  addEither ._+_ = Either

{-# COMPILE GHC Either = data Either (Left | Right) #-}

open import Agda.Builtin.List public
  using (List; [])
  renaming (_∷_ to _::_)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

--------------------------------------------------------------------------------
-- Wrapper types
--------------------------------------------------------------------------------

record Identity (A : Set) : Set where
  constructor identity:
  field runIdentity : A

open Identity public

record All : Set where
  constructor all:
  field getAll : Bool

open All public

record Any : Set where
  constructor any:
  field getAny : Bool

open Any public

record Sum (A : Set) : Set where
  constructor sum:
  field getSum : A

open Sum public

record Product (A : Set) : Set where
  constructor product:
  field getProduct : A

open Product public

record First (A : Set) : Set where
  constructor first:
  field getFirst : Maybe A

open First public

record Dual (A : Set) : Set where
  constructor dual:
  field getDual : A

open Dual public

record Endo A : Set where
  constructor endo:
  field appEndo : A -> A

open Endo public

--------------------------------------------------------------------------------
-- Basic functions
--------------------------------------------------------------------------------

infixr 0 _$_
infixl 1 _#_
infixr 5 _<<<_ _>>>_

flip : (A -> B -> C) -> B -> A -> C
flip f b a = f a b

identity : A -> A
identity a = a

_$_ : (A -> B) -> A -> B
_$_ = identity

_#_ : A -> (A -> B) -> B
_#_ = flip _$_

_<<<_ : (B -> C) -> (A -> B) -> A -> C
g <<< f = \ a -> g (f a)

_>>>_ : (A -> B) -> (B -> C) -> A -> C
_>>>_ = flip _<<<_

const : A -> B -> A
const a _ = a

uncurry : (A -> B -> C) -> A * B -> C
uncurry f (a , b) = f a b

curry : (A * B -> C) -> A -> B -> C
curry f a b = f (a , b)

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Bool
--------------------------------------------------------------------------------

infix 0 if_then_else_
infixr 5 _||_
infixr 6 _&&_

bool : A -> A -> Bool -> A
bool a _ false = a
bool _ a true = a

if_then_else_ : Bool -> A -> A -> A
if b then t else f = bool f t b

not : Bool -> Bool
not true  = false
not false = true

_&&_ : Bool -> Bool -> Bool
true && b = b
false && _ = false

_||_ : Bool -> Bool -> Bool
true || _ = true
false || b = b

Assert : Bool -> Set
Assert true = Unit
Assert false = Void

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Nat
--------------------------------------------------------------------------------

instance
  addNat : Add Nat
  addNat ._+_ = Agda.Builtin.Nat._+_

  subNat : Sub Nat
  subNat ._-_ = Agda.Builtin.Nat._-_

  mulNat : Mul Nat
  mulNat ._*_ = Agda.Builtin.Nat._*_

  divNat : Div Nat
  divNat = record {
      Constraint = \ { zero -> Void; (suc n) -> Unit };
      _/_ = \ { m (suc n) -> Agda.Builtin.Nat.div-helper zero n m n }
    }

  Mod:Nat : Mod Nat
  Mod:Nat = record {
      Constraint = \ { zero -> Void; (suc n) -> Unit };
      _%_ = \ { m (suc n) -> Agda.Builtin.Nat.mod-helper zero n m n }
    }

  Number:Nat : Number Nat
  Number:Nat = record {
      Constraint = const Unit;
      fromNat = \ n -> n
    }

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ 0 = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

foldN : A -> (A -> A) -> Nat -> A
foldN a f = natrec a (const f)

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Int
--------------------------------------------------------------------------------

instance
  addInt : Add Int
  addInt ._+_ = add
    where
      -- Subtracting two naturals to an integer result.
      sub : Nat -> Nat -> Int
      sub m 0 = pos m
      sub 0 (suc n) = negsuc n
      sub (suc m) (suc n) = sub m n

      add : Int -> Int -> Int
      add (negsuc m) (negsuc n) = negsuc (suc (m + n))
      add (negsuc m) (pos n) = sub n (suc m)
      add (pos m) (negsuc n) = sub m (suc n)
      add (pos m) (pos n) = pos (m + n)

  negationInt : Negation Int
  negationInt .-_ = \ where
    (pos zero) -> pos zero
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)

  subInt : Sub Int
  subInt ._-_ n m = n + (- m)

  mulInt : Mul Int
  mulInt ._*_ = \ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> - (pos (n * suc m))
    (negsuc n) (pos m) -> - (pos (suc n * m))

foldZ : (Nat -> A) -> (Nat -> A) -> Int -> A
foldZ f g (pos n) = f n
foldZ f g (negsuc n) = g n

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Char
--------------------------------------------------------------------------------

open import Agda.Builtin.Char public
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

--------------------------------------------------------------------------------
-- Basic operations/functions regarding String
--------------------------------------------------------------------------------

unpack = Agda.Builtin.String.primStringToList
pack = Agda.Builtin.String.primStringFromList

instance
  appendString : Append String String String
  appendString ._++_ = Agda.Builtin.String.primStringAppend

  IsString:String : IsString String
  IsString:String = record {
      Constraint = const Unit;
      fromString = \ s -> s
    }

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Float
--------------------------------------------------------------------------------

instance
  addFloat : Add Float
  addFloat ._+_ = Agda.Builtin.Float.primFloatPlus

  subFloat : Sub Float
  subFloat ._-_ = Agda.Builtin.Float.primFloatMinus

  negationFloat : Negation Float
  negationFloat .-_ = Agda.Builtin.Float.primFloatNegate

  mulFloat : Mul Float
  mulFloat ._*_ = Agda.Builtin.Float.primFloatTimes

  divFloat : Div Float
  divFloat = record {
      Constraint = const Unit;
      _/_ = \ x y -> Agda.Builtin.Float.primFloatDiv x y
    }

--------------------------------------------------------------------------------
-- Basic operations regarding Pair
--------------------------------------------------------------------------------

split : (A -> B) -> (A -> C) -> A -> B * C
split f g a = (f a , g a)

cross : (A -> B) -> (C -> D) -> A * C -> B * D
cross f g = split (f <<< fst) (g <<< snd)

swap : A * B -> B * A
swap = split snd fst

dupe : A -> A * A
dupe = split identity identity

apply : (A -> B) * A -> B
apply = uncurry _$_

--------------------------------------------------------------------------------
-- Basic operations regarding Either
--------------------------------------------------------------------------------

either : (A -> C) -> (B -> C) -> A + B -> C
either f g (left x) = f x
either f g (right y) = g y

plus : (A -> B) -> (C -> D) -> A + C -> B + D
plus f g = either (left <<< f) (right <<< g)

mirror : A + B -> B + A
mirror = either right left

untag : A + A -> A
untag = either identity identity

isLeft : A + B -> Bool
isLeft = either (const true) (const false)

isRight : A + B -> Bool
isRight = not <<< isLeft

fromLeft : A -> A + B -> A
fromLeft x = either identity (const x)

fromRight : B -> A + B -> B
fromRight y = either (const y) identity

-------------------------------------------------------------------------------
-- Basic operations regarding List
--------------------------------------------------------------------------------

pattern singleton a = a :: []

instance
  appendList : forall {A} -> Append (List A) (List A) (List A)
  appendList ._++_ [] ys = ys
  appendList ._++_ (x :: xs) ys = x :: xs ++ ys

---------------------------------------------------------------------------------
-- Basic operations regarding Maybe
--------------------------------------------------------------------------------

maybe : B -> (A -> B) -> Maybe A -> B
maybe b f nothing = b
maybe b f (just a) = f a

fromMaybe : A -> Maybe A -> A
fromMaybe = flip maybe identity

maybeToLeft : B -> Maybe A -> A + B
maybeToLeft b = maybe (right b) left

maybeToRight : B -> Maybe A -> B + A
maybeToRight b = maybe (left b) right

maybeToList : Maybe A -> List A
maybeToList = maybe [] singleton

listToMaybe : List A -> Maybe A
listToMaybe [] = nothing
listToMaybe (a :: _) = just a

--------------------------------------------------------------------------------
-- Eq and Ord
--------------------------------------------------------------------------------

record Eq (A : Set) : Set where
  infix 4 _==_ _/=_
  field
    _==_ : A -> A -> Bool

  _/=_ : A -> A -> Bool
  x /= y with x == y
  ... | true = false
  ... | false = true

open Eq {{...}} public

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (A : Set) : Set where
  field
    overlap {{eq}} : Eq A
    compare : A -> A -> Ordering

  _<_ : A -> A -> Bool
  x < y with compare x y
  ... | LT = true
  ... | _ = false

  _<=_ : A -> A -> Bool
  x <= y with compare x y
  ... | LT = true
  ... | EQ = true
  ... | _ = false

  _>_ : A -> A -> Bool
  x > y = y < x

  _>=_ : A -> A -> Bool
  x >= y = y <= x

  min : A -> A -> A
  min x y with compare x y
  ... | LT = x
  ... | EQ = x
  ... | GT = y

  max : A -> A -> A
  max x y with compare x y
  ... | LT = y
  ... | EQ = y
  ... | GT = x

open Ord {{...}} public

comparing : {{_ : Ord B}} -> (A -> B) -> A -> A -> Ordering
comparing p x y = compare (p x) (p y)

--------------------------------------------------------------------------------
-- Semigroup and Monoid
--------------------------------------------------------------------------------

record Semigroup (A : Set) : Set where
  infixr 6 _<>_
  field _<>_ : A -> A -> A

open Semigroup {{...}} public

record Monoid (A : Set) : Set where
  field
    overlap {{semigroup}} : Semigroup A
    empty : A

open Monoid {{...}} public

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

record Show (A : Set) : Set where
  field
    show : A -> String

open Show {{...}} public

--------------------------------------------------------------------------------
-- Functor
--------------------------------------------------------------------------------

infixl 24 _<$>_
infixr 2 _~>_

record Functor (F : Set -> Set) : Set where
  field
    map : (A -> B) -> (F A -> F B)

open Functor {{...}} public

_<$>_ : {{_ : Functor F}} -> (A -> B) -> F A -> F B
_<$>_ = map

_~>_ : (F G : Set -> Set) -> Set
F ~> G  = forall {A} -> F A -> G A

--------------------------------------------------------------------------------
-- Applicative
--------------------------------------------------------------------------------

record Applicative (F : Set -> Set) : Set where
  infixl 24 _<*>_ _*>_ _<*_
  field
    overlap {{super}} : Functor F
    _<*>_ : F (A -> B) -> F A -> F B
    pure : A -> F A

  _*>_ : F A -> F B -> F B
  a *> b = (| (flip const) a b |)

  _<*_ : F A -> F B -> F A
  a <* b = (| const a b |)

open Applicative {{...}} public

--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

record Monad (M : Set -> Set) : Set where
  infixl 1 _>>=_ _=<<_ _>>_ _<<_ _<=<_ _>=>_
  field
    overlap {{super}} : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B

  return : A -> M A
  return = pure

  _=<<_ : (A -> M B) -> M A -> M B
  _=<<_ = flip _>>=_

  join : M (M A) -> M A
  join = _=<<_ identity

  _>>_ : M A -> M B -> M B
  _>>_ = _*>_

  _<<_ : M A -> M B -> M A
  _<<_ = _<*_

  _<=<_ : (B -> M C) -> (A -> M B) -> A -> M C
  g <=< f = f >>> (_>>= g)

  _>=>_ : (A -> M B) -> (B -> M C) -> A -> M C
  _>=>_ = flip _<=<_

open Monad {{...}} public

--------------------------------------------------------------------------------
-- Eq instances
--------------------------------------------------------------------------------

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
  eqChar ._==_ c d = ord c == ord d

  eqString : Eq String
  eqString ._==_ = Agda.Builtin.String.primStringEquality

  eqPair : {{_ : Eq A}} {{_ : Eq B}} -> Eq (Pair A B)
  eqPair ._==_ (a , b) (c , d) = (a == c) && (b == d)

  eqEither : {{_ : Eq A}} {{_ : Eq B}} -> Eq (A + B)
  eqEither ._==_ = \ where
    (left x) (left y) -> x == y
    (right x) (right y) -> x == y
    _ _ -> false

  eqMaybe : {{_ : Eq A}} -> Eq (Maybe A)
  eqMaybe ._==_ = \ where
    nothing nothing -> true
    (just x) (just y) -> x == y
    _ _ -> false

  eqIdentity : {{_ : Eq A}} -> Eq (Identity A)
  eqIdentity ._==_ (identity: x) (identity: y) = x == y

--------------------------------------------------------------------------------
-- Ord instances
--------------------------------------------------------------------------------

instance
  ordVoid : Ord Void
  ordVoid .compare = \ ()

  ordUnit : Ord Unit
  ordUnit .compare unit unit = EQ

  ordNat : Ord Nat
  ordNat .compare m n = let _<_ = Agda.Builtin.Nat._<_ in
    if m < n then LT else if m == n then EQ else GT

  ordInt : Ord Int
  ordInt .compare = \ where
    (pos m) (pos n) -> compare m n
    (negsuc m) (negsuc n) -> compare m n
    (negsuc _) (pos _) -> LT
    (pos _) (negsuc _) -> GT

  ordFloat : Ord Float
  ordFloat .compare x y = let _<_ = Agda.Builtin.Float.primFloatNumericalLess in
    if x < y then LT else if x == y then EQ else GT

  ordIdentity : {{_ : Ord A}} -> Ord (Identity A)
  ordIdentity .compare (identity: x) (identity: y) = compare x y

--------------------------------------------------------------------------------
-- Functor instances
--------------------------------------------------------------------------------

instance
  functorPair : Functor (A *_)
  functorPair .map f (a , x) = (a , f x)

  functorEither : Functor (A +_)
  functorEither .map f = \ where
    (left a) -> left a
    (right x) -> right (f x)

  functorMaybe : Functor Maybe
  functorMaybe .map f = \ where
    nothing -> nothing
    (just a) -> just (f a)

  functorList : Functor List
  functorList .map f [] = []
  functorList .map f (x :: xs) = f x :: map f xs

  functorIdentity : Functor Identity
  functorIdentity .map f (identity: a) = identity: (f a)

--------------------------------------------------------------------------------
-- Applicative instances
--------------------------------------------------------------------------------

instance
  applicativeEither : Applicative (A +_)
  applicativeEither .pure = right
  applicativeEither ._<*>_ = \ where
    (left a) _ -> left a
    (right f) r -> map f r

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
    (f :: fs) (x :: xs) -> f x :: fs <*> xs

  applicativeIdentity : Applicative Identity
  applicativeIdentity .pure = identity:
  applicativeIdentity ._<*>_ (identity: f) x = map f x

--------------------------------------------------------------------------------
-- Monad instances
--------------------------------------------------------------------------------

instance
  monadEither : Monad (A +_)
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

  monadIdentity : Monad Identity
  monadIdentity ._>>=_ (identity: a) k = k a

--------------------------------------------------------------------------------
-- Semigroup instances
--------------------------------------------------------------------------------

instance
  semigroupDual : {{_ : Semigroup A}} -> Semigroup (Dual A)
  semigroupDual ._<>_ (dual: x) (dual: y) = dual: (y <> x)

  semigroupVoid : Semigroup Void
  semigroupVoid ._<>_ = \ ()

  semigroupUnit : Semigroup Unit
  semigroupUnit ._<>_ unit unit = unit

  semigroupAll : Semigroup All
  semigroupAll ._<>_ (all: x) (all: y) = all: (x && y)

  semigroupAny : Semigroup Any
  semigroupAny ._<>_ (any: x) (any: y) = any: (x || y)

  semigroupSum : Semigroup (Sum Nat)
  semigroupSum ._<>_ (sum: x) (sum: y) = sum: (x + y)

  semigroupProduct : Semigroup (Product Nat)
  semigroupProduct ._<>_ (product: x) (product: y) = product: (x * y)

  semigroupString : Semigroup String
  semigroupString ._<>_ = _++_

  semigroupMaybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  semigroupMaybe ._<>_ = \ where
    nothing m -> m
    m nothing -> m
    (just x) (just y) -> just (x <> y)

  semigroupList : Semigroup (List A)
  semigroupList ._<>_ = _++_

  semigroupFunction : {{_ : Semigroup B}} -> Semigroup (A -> B)
  semigroupFunction ._<>_ f g = \ a -> f a <> g a

  semigroupEndo : Semigroup (Endo A)
  semigroupEndo ._<>_ g f = endo: (appEndo g <<< appEndo f)

  semigroupFirst : Semigroup (First A)
  semigroupFirst ._<>_ x _ = x

--------------------------------------------------------------------------------
-- Monoid instances
--------------------------------------------------------------------------------

instance
  monoidDual : {{_ : Monoid A}} -> Monoid (Dual A)
  monoidDual .empty = dual: empty

  monoidUnit : Monoid Unit
  monoidUnit .empty = unit

  monoidAll : Monoid All
  monoidAll .empty = all: true

  monoidAny : Monoid Any
  monoidAny .empty = any: false

  monoidSum : Monoid (Sum Nat)
  monoidSum .empty = sum: 0

  monoidProduct : Monoid (Product Nat)
  monoidProduct .empty = product: 1

  monoidString : Monoid String
  monoidString .empty = ""

  monoidMaybe : {{_ : Monoid A}} -> Monoid (Maybe A)
  monoidMaybe .empty = nothing

  monoidList : Monoid (List A)
  monoidList .empty = []

  monoidFunction : {{_ : Monoid B}} -> Monoid (A -> B)
  monoidFunction .empty = const empty

  monoidEndo : Monoid (Endo A)
  monoidEndo .empty = endo: identity

  monoidFirst : Monoid (First A)
  monoidFirst .empty = first: nothing

--------------------------------------------------------------------------------
-- Show instances
--------------------------------------------------------------------------------

instance
  showUnit : Show Unit
  showUnit .show unit = "unit"

  showBool : Show Bool
  showBool .show = \ where
    true -> "true"
    false -> "false"

  showInt : Show Int
  showInt .show = Agda.Builtin.Int.primShowInteger

  showNat : Show Nat
  showNat .show n = show (pos n)

  showPair : {{_ : Show A}} {{_ : Show B}} -> Show (A * B)
  showPair .show (x , y) = "(" ++ show x ++ " , " ++ show y ++ ")"

  showEither : {{_ : Show A}} {{_ : Show B}} -> Show (A + B)
  showEither .show = \ where
    (left x) -> "left " ++ show x
    (right y) -> "right " ++ show y

  showMaybe : {{_ : Show A}} -> Show (Maybe A)
  showMaybe .show = \ where
    (just x) -> "just " ++ show x
    nothing -> "nothing"

  showList : {{_ : Show A}} -> Show (List A)
  showList .show = \ where
    [] -> "[]"
    (a :: as) -> show a ++ " :: " ++ show as

  showChar : Show Char
  showChar .show c = "'" ++ pack (singleton c) ++ "'"

  showString : Show String
  showString .show = Agda.Builtin.String.primShowString

  showFloat : Show Float
  showFloat .show = Agda.Builtin.Float.primShowFloat

--------------------------------------------------------------------------------
-- IO
--------------------------------------------------------------------------------

open import Agda.Builtin.IO public
  using (IO)

postulate
  mapIO : (A -> B) -> IO A -> IO B
  pureIO : A -> IO A
  apIO : IO (A -> B) -> IO A -> IO B
  bindIO : IO A -> (A -> IO B) -> IO B
  putStr : String -> IO Unit
  putStrLn : String -> IO Unit
  getLine : IO String
  getContents : IO String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC pureIO = \ _ a -> pure a #-}
{-# COMPILE GHC bindIO = \ _ _ ma f -> ma >>= f #-}
{-# COMPILE GHC putStr = Text.putStr #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC getContents = Text.getContents #-}

instance
  functorIO : Functor IO
  functorIO .map f io = bindIO io (f >>> pureIO)

  applicativeIO : Applicative IO
  applicativeIO .pure = pureIO
  applicativeIO ._<*>_ fs xs =
    bindIO fs (\ f -> bindIO xs (\ x -> pureIO (f x)))

  monadIO : Monad IO
  monadIO ._>>=_ = bindIO

  semigroupIO : {{_ : Semigroup A}} -> Semigroup (IO A)
  semigroupIO ._<>_ x y = (| _<>_ x y |)

  monoidIO : {{_ : Monoid A}} -> Monoid (IO A)
  monoidIO .empty = return empty

print : {{_ : Show A}} -> A -> IO Unit
print x = putStrLn (show x)

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStr (f s)
