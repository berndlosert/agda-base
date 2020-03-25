{-# OPTIONS --type-in-type #-}

module Prelude where

private
  variable
    A B C D : Set
    F G : Set -> Set

--------------------------------------------------------------------------------
-- Void, Unit and Bool
--------------------------------------------------------------------------------

data Void : Set where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit; tt to unit)

open import Agda.Builtin.Bool public
  using (Bool; true; false)

--------------------------------------------------------------------------------
-- Essential functions and operations
--------------------------------------------------------------------------------

identity : A -> A
identity a = a

const : A -> B -> A
const a _ = a

flip : (A -> B -> C) -> B -> A -> C
flip f b a = f a b

infixr 0 _$_
_$_ : (A -> B) -> A -> B
_$_ = identity

infixr 9 _<<<_
_<<<_ : (B -> C) -> (A -> B) -> A -> C
g <<< f = \ a -> g (f a)

infixr 9 _>>>_
_>>>_ : (A -> B) -> (B -> C) -> A -> C
_>>>_ = flip _<<<_

infix 0 if_then_else_
if_then_else_ : Bool -> A -> A -> A
if true then a else _ = a
if false then _ else a = a

not : Bool -> Bool
not true = false
not false = true

infixr 3 _&&_
_&&_ : Bool -> Bool -> Bool
true && b = b
false && _ = false

infixr 2 _||_
_||_ : Bool -> Bool -> Bool
true || _ = true
false || b = b

--------------------------------------------------------------------------------
-- For notational convenience
--------------------------------------------------------------------------------

record Add (A : Set) : Set where
  infixr 6 _+_
  field _+_ : A -> A -> A

open Add {{...}} public

record Negation (A : Set) : Set where
  field -_ : A -> A

open Negation {{...}} public

record Sub (A : Set) : Set where
  infixr 6 _-_
  field _-_ : A -> A -> A

open Sub {{...}} public

record Mul (A : Set) : Set where
  infixr 7 _*_
  field _*_ : A -> A -> A

open Mul {{...}} public

record Div (A : Set) : Set where
  infixr 7 _/_
  field
    Constraint : A -> Set
    _/_ : (x y : A) -> {_ : Constraint y} -> A

open Div {{...}} public

record Mod (A : Set) : Set where
  infixr 25 _%_
  field
    Constraint : A -> Set
    _%_ : (x y : A) -> {_ : Constraint y} -> A

open Mod {{...}} public

record Exp (A B C : Set) : Set where
  infixr 8 _^_
  field _^_ : A -> B -> C

open Exp {{...}} public

record Append A : Set where
  infixr 5 _++_
  field _++_ : A -> A -> A

open Append {{...}} public

open import Agda.Builtin.FromNat public
  using (Number; fromNat)

open import Agda.Builtin.FromNeg public
  using (Negative; fromNeg)

open import Agda.Builtin.FromString public
  using (IsString; fromString)

--------------------------------------------------------------------------------
-- Semigroup and Monoid
--------------------------------------------------------------------------------
record Semigroup (A : Set) : Set where
  infixr 5 _<>_
  field _<>_ : A -> A -> A

open Semigroup {{...}} public

record Monoid (A : Set) : Set where
  field
    overlap {{semigroup}} : Semigroup A
    empty : A

open Monoid {{...}} public

record Dual (A : Set) : Set where
  constructor dual:
  field getDual : A

open Dual public

instance
  semigroupDual : {{_ : Semigroup A}} -> Semigroup (Dual A)
  semigroupDual ._<>_ (dual: x) (dual: y) = dual: (y <> x)

  monoidDual : {{_ : Monoid A}} -> Monoid (Dual A)
  monoidDual .empty = dual: empty

-- For additive semigroups.
record Sum (A : Set) : Set where
  constructor sum:
  field getSum : A

open Sum public

-- For multiplicative semigroups.
record Product (A : Set) : Set where
  constructor product:
  field getProduct : A

open Product public

--------------------------------------------------------------------------------
-- Eq and Ord
--------------------------------------------------------------------------------

record Eq (A : Set) : Set where
  infix 4 _==_
  field
    _==_ : A -> A -> Bool

  infix 4 _/=_
  _/=_ : A -> A -> Bool
  x /= y = not (x == y)

open Eq {{...}} public

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (A : Set) : Set where
  infixl 4 _<_
  field
    overlap {{eq}} : Eq A
    _<_ : A -> A -> Bool

  compare : A -> A -> Ordering
  compare x y = if x < y then LT else if x == y then EQ else GT

  infixl 4 _<=_
  _<=_ : A -> A -> Bool
  x <= y = (x < y) || (x == y)

  infixl 4 _>_
  _>_ : A -> A -> Bool
  x > y = y < x

  infixl 4 _>=_
  _>=_ : A -> A -> Bool
  x >= y = y <= x

  min : A -> A -> A
  min x y = if x < y then x else y

  max : A -> A -> A
  max x y = if x < y then y else x

open Ord {{...}} public

comparing : {{_ : Ord B}} -> (A -> B) -> A -> A -> Ordering
comparing p x y = compare (p x) (p y)

--------------------------------------------------------------------------------
-- Functor
--------------------------------------------------------------------------------

record Functor (F : Set -> Set) : Set where
  field
    map : (A -> B) -> (F A -> F B)

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

infixr 0 _~>_
_~>_ : (F G : Set -> Set) -> Set
F ~> G  = forall {A} -> F A -> G A

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

  when : Bool -> F Unit -> F Unit
  when true x = x
  when false _ = pure unit

  unless : Bool -> F Unit -> F Unit
  unless false x = x
  unless true _ = pure unit

open Applicative {{...}} public

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
  join = _=<<_ identity

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

--------------------------------------------------------------------------------
-- Instances for Void
--------------------------------------------------------------------------------

instance
  eqVoid : Eq Void
  eqVoid ._==_ = \ ()

  ordVoid : Ord Void
  ordVoid ._<_ = \ ()

  semigroupVoid : Semigroup Void
  semigroupVoid ._<>_ = \ ()

--------------------------------------------------------------------------------
-- Instances for Unit
--------------------------------------------------------------------------------

instance
  eqUnit : Eq Unit
  eqUnit ._==_ unit unit = true

  ordUnit : Ord Unit
  ordUnit ._<_ unit unit = false

  semigroupUnit : Semigroup Unit
  semigroupUnit ._<>_ unit unit = unit

  monoidUnit : Monoid Unit
  monoidUnit .empty = unit

--------------------------------------------------------------------------------
-- Innstances for Bool and wrappers Any, All
--------------------------------------------------------------------------------

record All : Set where
  constructor all:
  field getAll : Bool

open All public

record Any : Set where
  constructor any:
  field getAny : Bool

open Any public

instance
  eqBool : Eq Bool
  eqBool ._==_ = \ where
    true true -> true
    false false -> false
    _ _ -> false

  semigroupAll : Semigroup All
  semigroupAll ._<>_ (all: x) (all: y) = all: (x && y)

  semigroupAny : Semigroup Any
  semigroupAny ._<>_ (any: x) (any: y) = any: (x || y)

  monoidAll : Monoid All
  monoidAll .empty = all: true

  monoidAny : Monoid Any
  monoidAny .empty = any: false

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

open import Agda.Builtin.Nat public
  using (Nat; zero; suc)

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ 0 = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

applyN : (A -> A) -> Nat -> A -> A
applyN f n a = natrec a (const f) n

instance
  eqNat : Eq Nat
  eqNat ._==_ = Agda.Builtin.Nat._==_

  ordNat : Ord Nat
  ordNat ._<_ = Agda.Builtin.Nat._<_

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

  modNat : Mod Nat
  modNat = record {
      Constraint = \ { zero -> Void; (suc n) -> Unit };
      _%_ = \ { m (suc n) -> Agda.Builtin.Nat.mod-helper zero n m n }
    }

  numberNat : Number Nat
  numberNat = record {
      Constraint = const Unit;
      fromNat = \ n -> n
    }

  semigroupSum : Semigroup (Sum Nat)
  semigroupSum ._<>_ (sum: x) (sum: y) = sum: (x + y)

  semigroupProduct : Semigroup (Product Nat)
  semigroupProduct ._<>_ (product: x) (product: y) = product: (x * y)

  monoidSum : Monoid (Sum Nat)
  monoidSum .empty = sum: 0

  monoidProduct : Monoid (Product Nat)
  monoidProduct .empty = product: 1

--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------

open import Agda.Builtin.Int public
  using (Int; pos; negsuc)

foldZ : (Nat -> A) -> (Nat -> A) -> Int -> A
foldZ f g (pos n) = f n
foldZ f g (negsuc n) = g n

instance
  eqInt : Eq Int
  eqInt ._==_ = \ where
    (pos m) (pos n) -> m == n
    (negsuc m) (negsuc n) -> m == n
    _ _ -> false

  ordInt : Ord Int
  ordInt ._<_ = \ where
    (pos m) (pos n) -> m < n
    (negsuc m) (negsuc n) -> m > n
    (negsuc _) (pos _) -> true
    (pos _) (negsuc _) -> false

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

--------------------------------------------------------------------------------
-- Float
--------------------------------------------------------------------------------

open import Agda.Builtin.Float public
  using (Float)

instance
  eqFloat : Eq Float
  eqFloat ._==_ = Agda.Builtin.Float.primFloatNumericalEquality

  ordFloat : Ord Float
  ordFloat ._<_ = Agda.Builtin.Float.primFloatNumericalLess

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
-- Char
--------------------------------------------------------------------------------

open import Agda.Builtin.Char public
  using (Char)
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

instance
  eqChar : Eq Char
  eqChar ._==_ c d = let ord = Agda.Builtin.Char.primCharToNat in
    ord c == ord d

--------------------------------------------------------------------------------
-- String
--------------------------------------------------------------------------------

open import Agda.Builtin.String public
  using (String)
  renaming (
    primStringToList to unpack;
    primStringFromList to pack
  )

instance
  eqString : Eq String
  eqString ._==_ = Agda.Builtin.String.primStringEquality

  appendString : Append String
  appendString ._++_ = Agda.Builtin.String.primStringAppend

  isStringString : IsString String
  isStringString = record {
      Constraint = const Unit;
      fromString = \ s -> s
    }

  semigroupString : Semigroup String
  semigroupString ._<>_ = _++_

  monoidString : Monoid String
  monoidString .empty = ""

--------------------------------------------------------------------------------
-- Pair
--------------------------------------------------------------------------------

infixr 4 _,_
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair public

{-# FOREIGN GHC type AgdaPair a b = (a, b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Prelude.AgdaPair ((,)) #-}

instance mulSet : Mul Set
mulSet ._*_ = Pair

split : (A -> B) -> (A -> C) -> A -> B * C
split f g a = (f a , g a)

cross : (A -> B) -> (C -> D) -> A * C -> B * D
cross f g = split (f <<< fst) (g <<< snd)

swap : A * B -> B * A
swap = split snd fst

dupe : A -> A * A
dupe = split identity identity

uncurry : (A -> B -> C) -> A * B -> C
uncurry f (a , b) = f a b

curry : (A * B -> C) -> A -> B -> C
curry f a b = f (a , b)

apply : (A -> B) * A -> B
apply = uncurry _$_

instance
  eqPair : {{_ : Eq A}} {{_ : Eq B}} -> Eq (A * B)
  eqPair ._==_ (a , b) (c , d) = (a == c) && (b == d)

  functorPair : Functor (A *_)
  functorPair .map f (a , x) = (a , f x)

--------------------------------------------------------------------------------
-- Either
--------------------------------------------------------------------------------

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

{-# COMPILE GHC Either = data Either (Left | Right) #-}

instance addSet : Add Set
addSet ._+_ = Either

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

instance
  eqEither : {{_ : Eq A}} {{_ : Eq B}} -> Eq (A + B)
  eqEither ._==_ = \ where
    (left x) (left y) -> x == y
    (right x) (right y) -> x == y
    _ _ -> false

  functorEither : Functor (A +_)
  functorEither .map f = \ where
    (left a) -> left a
    (right x) -> right (f x)

  applicativeEither : Applicative (A +_)
  applicativeEither .pure = right
  applicativeEither ._<*>_ = \ where
    (left a) _ -> left a
    (right f) r -> map f r

  monadEither : Monad (A +_)
  monadEither ._>>=_ = \ where
    (left a) k -> left a
    (right x) k -> k x

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

maybe : B -> (A -> B) -> Maybe A -> B
maybe b f nothing = b
maybe b f (just a) = f a

fromMaybe : A -> Maybe A -> A
fromMaybe = flip maybe identity

maybeToLeft : B -> Maybe A -> A + B
maybeToLeft b = maybe (right b) left

maybeToRight : B -> Maybe A -> B + A
maybeToRight b = maybe (left b) right

record First (A : Set) : Set where
  constructor first:
  field getFirst : Maybe A

open First public

instance
  eqMaybe : {{_ : Eq A}} -> Eq (Maybe A)
  eqMaybe ._==_ = \ where
    nothing nothing -> true
    (just x) (just y) -> x == y
    _ _ -> false

  functorMaybe : Functor Maybe
  functorMaybe .map f = \ where
    nothing -> nothing
    (just a) -> just (f a)

  applicativeMaybe : Applicative Maybe
  applicativeMaybe .pure = just
  applicativeMaybe ._<*>_ = \ where
    (just f) m -> map f m
    nothing _ -> nothing

  monadMaybe : Monad Maybe
  monadMaybe ._>>=_ = \ where
    nothing k -> nothing
    (just x) k -> k x

  semigroupMaybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  semigroupMaybe ._<>_ = \ where
    nothing m -> m
    m nothing -> m
    (just x) (just y) -> just (x <> y)

  monoidMaybe : {{_ : Monoid A}} -> Monoid (Maybe A)
  monoidMaybe .empty = nothing

  semigroupFirst : Semigroup (First A)
  semigroupFirst ._<>_ (first: x) (first: y) with x | y
  ... | nothing | m = first: m
  ... | (just a) | _ = first: (just a)

  monoidFirst : Monoid (First A)
  monoidFirst .empty = first: nothing

--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

open import Agda.Builtin.List public
  using (List; [])
  renaming (_∷_ to _::_)

instance
  appendList : Append (List A)
  appendList ._++_ [] ys = ys
  appendList ._++_ (x :: xs) ys = x :: xs ++ ys

  functorList : Functor List
  functorList .map f [] = []
  functorList .map f (x :: xs) = f x :: map f xs

  applicativeList : Applicative List
  applicativeList .pure x = x :: []
  applicativeList ._<*>_ = \ where
    [] _ -> []
    _ [] -> []
    (f :: fs) (x :: xs) -> f x :: (fs <*> xs)

  monadList : Monad List
  monadList ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x ++ (xs >>= k)

  semigroupList : Semigroup (List A)
  semigroupList ._<>_ = _++_

  monoidList : Monoid (List A)
  monoidList .empty = []

foldr : (A -> B -> B) -> B -> List A -> B
foldr f b [] = b
foldr f b (a :: as) = f a (foldr f b as)

foldl : (B -> A -> B) -> B -> List A -> B
foldl f b [] = b
foldl f b (a :: as) = foldl f (f b a) as

foldMap : {{_ : Monoid B}} -> (A -> B) -> List A -> B
foldMap f = foldr (\ x y -> f x <> y) empty

fold : {{_ : Monoid A}} -> List A -> A
fold = foldMap identity

uncons : List A -> Maybe (A * List A)
uncons [] = nothing
uncons (a :: as) = just (a , as)

recons : Maybe (A * List A) -> List A
recons = maybe [] (uncurry _::_)

replicate : Nat -> A -> List A
replicate n a = applyN (a ::_) n []

til : Nat -> List Nat
til 0 = []
til (suc n) = til n ++ pure n

range : Nat -> Nat -> List Nat
range m n with compare m n
... | GT = []
... | EQ = pure n
... | LT = map (_+ m) $ til $ suc (n - m)

maybeToList : Maybe A -> List A
maybeToList = maybe [] pure

listToMaybe : List A -> Maybe A
listToMaybe [] = nothing
listToMaybe (a :: _) = just a

head : List A -> Maybe A
head [] = nothing
head (a :: as) = just a

tail : List A -> Maybe (List A)
tail [] = nothing
tail (a :: as) = just as

--------------------------------------------------------------------------------
-- Function
--------------------------------------------------------------------------------

Function : Set -> Set -> Set
Function A B = A -> B

record Endo A : Set where
  constructor endo:
  field appEndo : A -> A

open Endo public

instance
  semigroupFunction : {{_ : Semigroup B}} -> Semigroup (A -> B)
  semigroupFunction ._<>_ f g = \ a -> f a <> g a

  monoidFunction : {{_ : Monoid B}} -> Monoid (A -> B)
  monoidFunction .empty = const empty

  semigroupEndo : Semigroup (Endo A)
  semigroupEndo ._<>_ g f = endo: (appEndo g <<< appEndo f)

  monoidEndo : Monoid (Endo A)
  monoidEndo .empty = endo: identity

--------------------------------------------------------------------------------
-- Propositional equality
--------------------------------------------------------------------------------

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _===_)

--------------------------------------------------------------------------------
-- Identity
--------------------------------------------------------------------------------

record Identity (A : Set) : Set where
  constructor identity:
  field runIdentity : A

open Identity public

instance
  eqIdentity : {{_ : Eq A}} -> Eq (Identity A)
  eqIdentity ._==_ (identity: x) (identity: y) = x == y

  ordIdentity : {{_ : Ord A}} -> Ord (Identity A)
  ordIdentity ._<_ (identity: x) (identity: y) = x < y

  semigroupIdentity : {{_ : Semigroup A}} -> Semigroup (Identity A)
  semigroupIdentity ._<>_ (identity: x) (identity: y) = identity: (x <> y)

  monoidIdentity : {{_ : Monoid A}} -> Monoid (Identity A)
  monoidIdentity .empty = identity: empty

  functorIdentity : Functor Identity
  functorIdentity .map f (identity: a) = identity: (f a)

  applicativeIdentity : Applicative Identity
  applicativeIdentity .pure = identity:
  applicativeIdentity ._<*>_ (identity: f) x = map f x

  monadIdentity : Monad Identity
  monadIdentity ._>>=_ (identity: a) k = k a

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

record Show (A : Set) : Set where
  field
    show : A -> String

open Show {{...}} public

instance
  showVoid : Show Void
  showVoid .show ()

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
  showChar .show c = "'" ++ pack (pure c) ++ "'"

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
