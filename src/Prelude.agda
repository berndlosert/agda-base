{-# OPTIONS --type-in-type #-}

module Prelude where

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
  field
    _*_ : A -> A -> A

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
  field
    _^_ : A -> B -> C

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
  using (tt)
  renaming (⊤ to Unit)

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

Function : Set -> Set -> Set
Function A B = A -> B

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _===_)

record Pair (A B : Set) : Set where
  constructor Pair:
  field
    fst : A
    snd : B

open Pair public

instance
  Mul:Pair : Mul Set
  Mul:Pair ._*_ = Pair

{-# FOREIGN GHC type AgdaPair a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Prelude.AgdaPair ((,)) #-}
{-# DISPLAY Pair A B = A * B #-}

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

instance
  Add:Either : Add Set
  Add:Either ._+_ = Either

{-# COMPILE GHC Either = data Either (Left | Right) #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}
{-# DISPLAY Either A B = A + B #-}

open import Agda.Builtin.List public
  using (List; [])
  renaming (_∷_ to _::_)
  hiding (module List)

data Vector (A : Set) : Nat -> Set where
  [] : Vector A zero
  _::_ : forall {n} -> A -> Vector A n -> Vector A (suc n)

--------------------------------------------------------------------------------
-- Wrapper types
--------------------------------------------------------------------------------

record All : Set where
  constructor All:
  field
    get : Bool

record Any : Set where
  constructor Any:
  field
    get : Bool

record Sum (A : Set) : Set where
  constructor Sum:
  field
    get : A

record Product (A : Set) : Set where
  constructor Product:
  field
    get : A

record First (A : Set) : Set where
  constructor First:
  field
    get : Maybe A

record Dual (A : Set) : Set where
  constructor Dual:
  field
    get : A

--------------------------------------------------------------------------------
-- Basic functions
--------------------------------------------------------------------------------

infixr 0 _$_
infixl 1 _#_
infixr 5 _<<<_ _>>>_

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f y x = f x y

id : {A : Set} -> A -> A
id x = x

_$_ : {A B : Set} -> (A -> B) -> A -> B
_$_ = id

_#_ : {A B : Set} -> A -> (A -> B) -> B
_#_ = flip _$_

_<<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
g <<< f = \ x -> g (f x)

_>>>_ : {A B C : Set} -> (A -> B) -> (B -> C) -> A -> C
_>>>_ = flip _<<<_

const : {A B : Set} -> A -> B -> A
const x _ = x

uncurry : {A B C : Set} -> (A -> B -> C) -> A * B -> C
uncurry f (Pair: x y) = f x y

curry : {A B C : Set} -> (A * B -> C) -> A -> B -> C
curry f x y = f (Pair: x y)

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Bool
--------------------------------------------------------------------------------

infix 0 if_then_else_
infixr 5 _||_
infixr 6 _&&_

bool : {A : Set} -> A -> A -> Bool -> A
bool x y false = x
bool x y true = y

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if b then x else y = bool y x b

not : Bool -> Bool
not true  = false
not false = true

_&&_ : Bool -> Bool -> Bool
true && b = b
false && b = false

_||_ : Bool -> Bool -> Bool
true || b = true
false || b = b

Assert : Bool -> Set
Assert true = Unit
Assert false = Void

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Nat
--------------------------------------------------------------------------------

instance
  Add:Nat : Add Nat
  Add:Nat ._+_ = Agda.Builtin.Nat._+_

  Sub:Nat : Sub Nat
  Sub:Nat ._-_ = Agda.Builtin.Nat._-_

  Mul:Nat : Mul Nat
  Mul:Nat ._*_ = Agda.Builtin.Nat._*_

  Div:Nat : Div Nat
  Div:Nat = record {
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

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Int
--------------------------------------------------------------------------------

instance
  Add:Int : Add Int
  Add:Int ._+_ = add
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

  Negation:Int : Negation Int
  Negation:Int .-_ = \ where
    (pos zero) -> pos zero
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)

  Sub:Int : Sub Int
  Sub:Int ._-_ n m = n + (- m)

  Mul:Int : Mul Int
  Mul:Int ._*_ = \ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> - (pos (n * suc m))
    (negsuc n) (pos m) -> - (pos (suc n * m))

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
  Append:String : Append String String String
  Append:String ._++_ = Agda.Builtin.String.primStringAppend

  IsString:String : IsString String
  IsString:String = record {
      Constraint = const Unit;
      fromString = \ s -> s
    }

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Float
--------------------------------------------------------------------------------

instance
  Add:Float : Add Float
  Add:Float ._+_ = Agda.Builtin.Float.primFloatPlus

  Sub:Float : Sub Float
  Sub:Float ._-_ = Agda.Builtin.Float.primFloatMinus

  Negation:Float : Negation Float
  Negation:Float .-_ = Agda.Builtin.Float.primFloatNegate

  Mul:Float : Mul Float
  Mul:Float ._*_ = Agda.Builtin.Float.primFloatTimes

  Div:Float : Div Float
  Div:Float = record {
      Constraint = const Unit;
      _/_ = \ x y -> Agda.Builtin.Float.primFloatDiv x y
    }

--------------------------------------------------------------------------------
-- Functor
--------------------------------------------------------------------------------

record Functor (F : Set -> Set) : Set where
  field
    map : forall {A B} -> (A -> B) -> (F A -> F B)

open Functor {{...}} public

infixl 24 _<$>_

_<$>_ : forall {A B F} {{_ : Functor F}}
  -> (A -> B) -> F A -> F B
_<$>_ = map

infixr 2 _~>_

_~>_ : (F G : Set -> Set) -> Set
F ~> G  = forall {A} -> F A -> G A

--------------------------------------------------------------------------------
-- Applicative
--------------------------------------------------------------------------------

record Applicative (F : Set -> Set) : Set where
  infixl 24 _<*>_ _*>_ _<*_
  field
    overlap {{Functor:Applicative}} : Functor F
    _<*>_ : forall {A B} -> F (A -> B) -> F A -> F B
    pure : forall {A} -> A -> F A

  _*>_ : forall {A B} -> F A -> F B -> F B
  x *> y = (| (flip const) x y |)

  _<*_ : forall {A B} -> F A -> F B -> F A
  x <* y = (| const x y |)

open Applicative {{...}} public

--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

record Monad (M : Set -> Set) : Set where
  infixl 1 _>>=_ _=<<_ _<=<_ _>=>_
  field
    overlap {{Applicative:Monad}} : Applicative M
    _>>=_ : forall {A B} -> M A -> (A -> M B) -> M B

  return : forall {A} -> A -> M A
  return = pure

  _=<<_ : forall {A B} -> (A -> M B) -> M A -> M B
  _=<<_ = flip _>>=_

  join : forall {A} -> M (M A) -> M A
  join = _=<<_ id

  _<=<_ : forall {A B C : Set} -> (B -> M C) -> (A -> M B) -> A -> M C
  g <=< f = \ x -> f x >>= g

  _>=>_ : forall {A B C}-> (A -> M B) -> (B -> M C) -> A -> M C
  _>=>_ = flip _<=<_

open Monad {{...}} public

--------------------------------------------------------------------------------
-- Eq and Ord
--------------------------------------------------------------------------------

record Eq (A : Set) : Set where
  infix 4 _==_ _/=_
  field
    _==_ : A -> A -> Bool

  _/=_ : A -> A -> Bool
  x /= y = not (x == y)

open Eq {{...}} public

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (A : Set) : Set where
  field
    {{instance:Eq}} : Eq A
    _<_ : A -> A -> Bool

  compare : A -> A -> Ordering
  compare x y =
    if x == y then EQ else
    if x < y then LT else GT

  _<=_ : A -> A -> Bool
  x <= y = (x == y) || (x < y)

  _>_ : A -> A -> Bool
  x > y = y < x

  _>=_ : A -> A -> Bool
  x >= y = (x == y) || (x > y)

  min : A -> A -> A
  min x y = if x < y then x else y

  max : A -> A -> A
  max x y = if x > y then x else y

open Ord {{...}} public

comparing : {A B : Set} {{_ : Ord B}}
  -> (A -> B) -> A -> A -> Ordering
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
    overlap {{Semigroup:Monoid}} : Semigroup A
    mempty : A

open Monoid {{...}} public

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

record Show (A : Set) : Set where
  field
    show : A -> String

open Show {{...}} public

--------------------------------------------------------------------------------
-- Basic operations regarding List and Vector
--------------------------------------------------------------------------------

pattern [_] x1 =
  x1 :: []
pattern [_,_] x1 x2 =
  x1 :: x2 :: []
pattern [_,_,_] x1 x2 x3 =
  x1 :: x2 :: x3 :: []
pattern [_,_,_,_] x1 x2 x3 x4 =
  x1 :: x2 :: x3 :: x4 :: []
pattern [_,_,_,_,_] x1 x2 x3 x4 x5 =
  x1 :: x2 :: x3 :: x4 :: x5 :: []
pattern [_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: []
pattern [_,_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 x7 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: []
pattern [_,_,_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 x7 x8 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: []
pattern [_,_,_,_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 x7 x8 x9 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: []
pattern [_,_,_,_,_,_,_,_,_,_] x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =
  x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: []

instance
  Append:List : forall {A} -> Append (List A) (List A) (List A)
  Append:List ._++_ [] ys = ys
  Append:List ._++_ (x :: xs) ys = x :: xs ++ ys

  Append:Vector : forall {m n A}
    -> Append (Vector A m) (Vector A n) (Vector A (m + n))
  Append:Vector ._++_ [] ys = ys
  Append:Vector ._++_ (x :: xs) ys = x :: xs ++ ys

--------------------------------------------------------------------------------
-- Eq instances
--------------------------------------------------------------------------------

instance
  Eq:Void : Eq Void
  Eq:Void ._==_ = \ ()

  Eq:Unit : Eq Unit
  Eq:Unit ._==_ tt tt = true

  Eq:Bool : Eq Bool
  Eq:Bool ._==_ = \ where
    true true -> true
    false false -> false
    _ _ -> false

  Eq:Nat : Eq Nat
  Eq:Nat ._==_ = Agda.Builtin.Nat._==_

  Eq:Int : Eq Int
  Eq:Int ._==_ = \ where
    (pos m) (pos n) -> m == n
    (negsuc m) (negsuc n) -> m == n
    _ _ -> false

  Eq:Float : Eq Float
  Eq:Float ._==_ = Agda.Builtin.Float.primFloatNumericalEquality

  Eq:Char : Eq Char
  Eq:Char ._==_ c c' = ord c == ord c'

  Eq:String : Eq String
  Eq:String ._==_ = Agda.Builtin.String.primStringEquality

  Eq:Pair : forall {A B} {{_ : Eq A}} {{_ : Eq B}} -> Eq (Pair A B)
  Eq:Pair ._==_ (Pair: x y) (Pair: x' y') = (x == x') && (y == y')

  Eq:Either : forall {A B} {{_ : Eq A}} {{_ : Eq B}} -> Eq (A + B)
  Eq:Either ._==_ = \ where
    (left x) (left x') -> x == x'
    (right y) (right y') -> y == y'
    _ _ -> false

  Eq:Maybe : forall {A} {{_ : Eq A}} -> Eq (Maybe A)
  Eq:Maybe ._==_ = \ where
    nothing nothing -> true
    (just x) (just x') -> x == x'
    _ _ -> false

--------------------------------------------------------------------------------
-- Ord instances
--------------------------------------------------------------------------------

instance
  Ord:Void : Ord Void
  Ord:Void ._<_ = \ ()

  Ord:Unit : Ord Unit
  Ord:Unit ._<_ tt tt = false

  Ord:Nat : Ord Nat
  Ord:Nat ._<_ = Agda.Builtin.Nat._<_

  Ord:Int : Ord Int
  Ord:Int ._<_ = \ where
    (pos m) (pos n) -> m < n
    (negsuc m) (negsuc n) -> n < m
    (pos _) (negsuc _) -> false
    (negsuc _) (pos _) -> true

  Ord:Float : Ord Float
  Ord:Float ._<_ = Agda.Builtin.Float.primFloatNumericalLess

--------------------------------------------------------------------------------
-- Functor instances
--------------------------------------------------------------------------------

instance
  Functor:Pair : forall {A} -> Functor (A *_)
  Functor:Pair .map f (Pair: x y) = Pair: x (f y)

  Functor:Either : forall {A} -> Functor (A +_)
  Functor:Either .map f = \ where
    (left x) -> left x
    (right y) -> right (f y)

  Functor:Maybe : Functor Maybe
  Functor:Maybe .map f = \ where
    nothing -> nothing
    (just x) -> just (f x)

  Functor:List : Functor List
  Functor:List .map f [] = []
  Functor:List .map f (x :: xs) = f x :: map f xs

--------------------------------------------------------------------------------
-- Applicative instances
--------------------------------------------------------------------------------

instance
  Applicative:Either : forall {A} -> Applicative (A +_)
  Applicative:Either = \ where
    .pure -> right
    ._<*>_ (left x) _ -> left x
    ._<*>_ (right f) r -> map f r

  Applicative:Maybe : Applicative Maybe
  Applicative:Maybe = \ where
    .pure -> just
    ._<*>_ (just f) m -> map f m
    ._<*>_ nothing _ -> nothing

  Applicative:List : Applicative List
  Applicative:List .pure = [_]
  Applicative:List ._<*>_ = \ where
    [] _ -> []
    _ [] -> []
    (f :: fs) (x :: xs) -> f x :: fs <*> xs

--------------------------------------------------------------------------------
-- Monad instances
--------------------------------------------------------------------------------

instance
  Monad:Either : forall {A} -> Monad (A +_)
  Monad:Either ._>>=_ = \ where
    (left x) k -> left x
    (right y) k -> k y

  Monad:Maybe : Monad Maybe
  Monad:Maybe ._>>=_ = \ where
    nothing k -> nothing
    (just x) k -> k x

  Monad:List : Monad List
  Monad:List ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x ++ (xs >>= k)

--------------------------------------------------------------------------------
-- Semigroup instances
--------------------------------------------------------------------------------

instance
  Semigroup:Dual : forall {A} {{_ : Semigroup A}} -> Semigroup (Dual A)
  Semigroup:Dual ._<>_ (Dual: x) (Dual: y) = Dual: (y <> x)

  Semigroup:Void : Semigroup Void
  Semigroup:Void ._<>_ = \ ()

  Semigroup:Unit : Semigroup Unit
  Semigroup:Unit ._<>_ tt tt = tt

  Semigroup:All : Semigroup All
  Semigroup:All ._<>_ (All: x) (All: y) = All: (x && y)

  Semigroup:Any : Semigroup Any
  Semigroup:Any ._<>_ (Any: x) (Any: y) = Any: (x || y)

  Semigroup:Sum : Semigroup (Sum Nat)
  Semigroup:Sum ._<>_ (Sum: x) (Sum: y) = Sum: (x + y)

  Semigroup:Product : Semigroup (Product Nat)
  Semigroup:Product ._<>_ (Product: x) (Product: y) = Product: (x * y)

  Semigroup:String : Semigroup String
  Semigroup:String ._<>_ = _++_

  Semigroup:Maybe : forall {A} {{_ : Semigroup A}} -> Semigroup (Maybe A)
  Semigroup:Maybe ._<>_ = \ where
    nothing y -> y
    x nothing -> x
    (just x) (just y) -> just (x <> y)

  Semigroup:List : forall {A} -> Semigroup (List A)
  Semigroup:List ._<>_ = _++_

  Semigroup:Function : {A B : Set} {{_ : Semigroup B}} -> Semigroup (A -> B)
  Semigroup:Function ._<>_ f g = \ x -> f x <> g x

  Semigroup:<<< : forall {A} -> Semigroup (A -> A)
  Semigroup:<<< ._<>_ = _<<<_

  Semigroup:First : forall {A} -> Semigroup (First A)
  Semigroup:First ._<>_ x _ = x

--------------------------------------------------------------------------------
-- Monoid instances
--------------------------------------------------------------------------------

instance
  Monoid:Dual : forall {A} {{_ : Monoid A}} -> Monoid (Dual A)
  Monoid:Dual .mempty = Dual: mempty

  Monoid:Unit : Monoid Unit
  Monoid:Unit .mempty = tt

  Monoid:All : Monoid All
  Monoid:All .mempty = All: true

  Monoid:Any : Monoid Any
  Monoid:Any .mempty = Any: false

  Monoid:Sum : Monoid (Sum Nat)
  Monoid:Sum .mempty = Sum: 0

  Monoid:Product : Monoid (Product Nat)
  Monoid:Product .mempty = Product: 1

  Monoid:String : Monoid String
  Monoid:String .mempty = ""

  Monoid:Maybe : forall {A} {{_ : Monoid A}} -> Monoid (Maybe A)
  Monoid:Maybe .mempty = nothing

  Monoid:List : forall {A} -> Monoid (List A)
  Monoid:List .mempty = []

  Monoid:Function : {A B : Set} {{_ : Monoid B}} -> Monoid (A -> B)
  Monoid:Function .mempty = const mempty

  Monoid:<<< : forall {A} -> Monoid (A -> A)
  Monoid:<<< = \ where
    .Semigroup:Monoid -> Semigroup:<<<
    .mempty -> id

  Monoid:First : forall {A} -> Monoid (First A)
  Monoid:First .mempty = First: nothing

--------------------------------------------------------------------------------
-- Show instances
--------------------------------------------------------------------------------

instance
  Show:Unit : Show Unit
  Show:Unit .show tt = "tt"

  Show:Bool : Show Bool
  Show:Bool .show = \ where
    true -> "true"
    false -> "false"

  Show:Int : Show Int
  Show:Int .show = Agda.Builtin.Int.primShowInteger

  Show:Nat : Show Nat
  Show:Nat .show n = show (pos n)

  Show:Pair : forall {A B} {{_ : Show A}} {{_ : Show B}} -> Show (A * B)
  Show:Pair .show (Pair: x y) = "Pair: " ++ show x ++ " " ++ show y

  Show:Either : forall {A B} {{_ : Show A}} {{_ : Show B}} -> Show (A + B)
  Show:Either .show = \ where
    (left x) -> "left " ++ show x
    (right y) -> "right " ++ show y

  Show:Maybe : {A : Set} {{_ : Show A}} -> Show (Maybe A)
  Show:Maybe .show = \ where
    (just x) -> "just " ++ show x
    nothing -> "nothing"

  Show:List : forall {A} {{_ : Show A}} -> Show (List A)
  Show:List .show = \ { [] -> "[]"; xs -> "[ " ++ csv xs ++ " ]" }
    where
      csv : {A : Set} {{_ : Show A}} -> List A -> String
      csv [] = ""
      csv (x :: []) = show x
      csv (x :: xs) = show x ++ " , " ++ csv xs

  Show:Char : Show Char
  Show:Char .show c = "'" ++ pack [ c ] ++ "'"

  Show:String : Show String
  Show:String .show = Agda.Builtin.String.primShowString

  Show:Float : Show Float
  Show:Float .show = Agda.Builtin.Float.primShowFloat

--------------------------------------------------------------------------------
-- IO
--------------------------------------------------------------------------------

open import Agda.Builtin.IO public
  using (IO)

postulate
  mapIO : {A B : Set} -> (A -> B) -> IO A -> IO B
  pureIO : {A : Set} -> A -> IO A
  apIO : {A B : Set} -> IO (A -> B) -> IO A -> IO B
  bindIO : {A B : Set} -> IO A -> (A -> IO B) -> IO B
  putStr : String -> IO Unit
  putStrLn : String -> IO Unit
  getLine : IO String
  getContents : IO String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC mapIO = \ _ _ f -> map f #-}
{-# COMPILE GHC apIO = \ _ _ mf ma -> ap mf ma #-}
{-# COMPILE GHC pureIO = \ _ a -> pure a #-}
{-# COMPILE GHC bindIO = \ _ _ ma f -> ma >>= f #-}
{-# COMPILE GHC putStr = Text.putStr #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC getContents = Text.getContents #-}

instance
  Functor:IO : Functor IO
  Functor:IO .map = mapIO

  Applicative:IO : Applicative IO
  Applicative:IO = \ where
    .pure -> pureIO
    ._<*>_ -> apIO

  Monad:IO : Monad IO
  Monad:IO ._>>=_ = bindIO

  Semigroup:IO : forall {A} {{_ : Semigroup A}} -> Semigroup (IO A)
  Semigroup:IO ._<>_ x y = (| _<>_ x y |)

  Monoid:IO : forall {A} {{_ : Monoid A}} -> Monoid (IO A)
  Monoid:IO .mempty = return mempty

print : forall {A} {{_ : Show A}} -> A -> IO Unit
print x = putStrLn (show x)

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStr (f s)
