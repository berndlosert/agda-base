{-# OPTIONS --type-in-type #-}

module Prelude where

--------------------------------------------------------------------------------
-- For notational convenience
--------------------------------------------------------------------------------

record Add (X : Set) : Set where
  infixr 24 _+_
  field _+_ : X -> X -> X

open Add {{...}} public

record Negation (X : Set) : Set where
  field -_ : X -> X

open Negation {{...}} public

record Sub (X : Set) : Set where
  infixr 24 _-_
  field _-_ : X -> X -> X

open Sub {{...}} public

record Mul (X : Set) : Set where
  infixr 25 _*_
  field
    _*_ : X -> X -> X

open Mul {{...}} public

record Div (X : Set) : Set where
  infixr 25 _/_
  field
    Constraint : X -> Set
    _/_ : (x y : X) -> {_ : Constraint y} -> X

open Div {{...}} hiding (Constraint) public

record Mod (X : Set) : Set where
  infixr 25 _%_
  field
    Constraint : X -> Set
    _%_ : (x y : X) -> {_ : Constraint y} -> X

open Mod {{...}} hiding (Constraint) public

record Exp (X Y Z : Set) : Set where
  infixr 50 _^_
  field
    _^_ : X -> Y -> Z

open Exp {{...}} public

-- Used for defining  dual or opposite categories, semigroups, monoids, etc.
record Dual (S : Set) : Set where
  field
     Op : S -> S

open Dual {{...}} public

record Append (X Y Z : Set) : Set where
  infixr 25 _++_
  field _++_ : X -> Y -> Z

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
Function X Y = X -> Y

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _===_)

record Pair (X Y : Set) : Set where
  constructor Pair:
  field
    fst : X
    snd : Y

open Pair public

instance
  Mul:Pair : Mul Set
  Mul:Pair ._*_ = Pair

{-# FOREIGN GHC type AgdaPair a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Prelude.AgdaPair ((,)) #-}
{-# DISPLAY Pair X Y = X * Y #-}

data Either (X Y : Set) : Set where
  left : X -> Either X Y
  right : Y -> Either X Y

instance
  Add:Either : Add Set
  Add:Either ._+_ = Either

{-# COMPILE GHC Either = data Either (Left | Right) #-}

data Maybe (X : Set) : Set where
  nothing : Maybe X
  just : X -> Maybe X

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}
{-# DISPLAY Either X Y = X + Y #-}

open import Agda.Builtin.List public
  using (List; [])
  renaming (_∷_ to _::_)
  hiding (module List)

data Vector (X : Set) : Nat -> Set where
  [] : Vector X zero
  _::_ : forall {n} -> X -> Vector X n -> Vector X (suc n)

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

record First (X : Set) : Set where
  constructor First:
  field
    get : Maybe X

--------------------------------------------------------------------------------
-- Utility functions
--------------------------------------------------------------------------------

infixr 0 _$_
infixl 1 _#_

flip : {X Y Z : Set} -> (X -> Y -> Z) -> Y -> X -> Z
flip f y x = f x y

_$_ : {X Y : Set} -> (X -> Y) -> X -> Y
f $ x = f x

_#_ : {X Y : Set} -> X -> (X -> Y) -> Y
x # f = f x

const : {X Y : Set} -> X -> Y -> X
const x _ = x

uncurry : {X Y Z : Set} -> (X -> Y -> Z) -> X * Y -> Z
uncurry f (Pair: x y) = f x y

curry : {X Y Z : Set} -> (X * Y -> Z) -> X -> Y -> Z
curry f x y = f (Pair: x y)

--------------------------------------------------------------------------------
-- Basic operations/functions regarding Bool
--------------------------------------------------------------------------------

infix 0 if_then_else_
infixr 5 _||_
infixr 6 _&&_

bool : {X : Set} -> X -> X -> Bool -> X
bool x y false = x
bool x y true = y

if_then_else_ : {X : Set} -> Bool -> X -> X -> X
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
-- Category
--------------------------------------------------------------------------------

record Category : Set where
  infixr 5 _<<<_ _>>>_
  field
    ob : Set
    hom : ob -> ob -> Set
    _<<<_ : forall {X Y Z} -> hom Y Z -> hom X Y -> hom X Z
    id : forall {X} -> hom X X

  _>>>_ : forall {X Y Z} -> hom X Y -> hom Y Z -> hom X Z
  f >>> g = g <<< f

open Category hiding (_<<<_; _>>>_; id) public
open Category {{...}} hiding (ob; hom) public

-- The category of types and total functions
instance
  Sets : Category
  Sets = \ where
    .ob -> Set
    .hom -> Function
    ._<<<_ g f -> \ x -> g (f x)
    .id x -> x

-- Dual categories
instance
  Dual:Category : Dual Category
  Dual:Category .Op C = let instance _ = C in \ where
    .ob -> ob C
    .hom X Y -> hom C Y X
    ._<<<_ -> _>>>_
    .id -> id

-- Product categories
instance
  Mul:Category : Mul Category
  Mul:Category ._*_ C C' =
    let instance _ = C; instance _ = C' in
    \ where
      .ob -> ob C * ob C'
      .hom (Pair: X X') (Pair: Y Y') -> hom C X Y * hom C' X' Y'
      ._<<<_ (Pair: g g') (Pair: f f') -> Pair: (g <<< f) (g' <<< f')
      .id -> Pair: id id

--------------------------------------------------------------------------------
-- FunctorOf
--------------------------------------------------------------------------------

record FunctorOf (C D : Category) (F : ob C -> ob D) : Set where
  field
    map : forall {X Y} -> hom C X Y -> hom D (F X) (F Y)

open FunctorOf {{...}} public

-- This case is so common, it deserves the shorter name.
Functor = FunctorOf Sets Sets

infixl 24 _<$>_

_<$>_ : forall {X Y F} {{_ : Functor F}}
  -> (X -> Y) -> F X -> F Y
_<$>_ = map

--------------------------------------------------------------------------------
-- Trans
--------------------------------------------------------------------------------

-- Squiggly arrows are used for (natural) transformations.
record Trans (C D : Category) : Set where
  infixr 2 _~>_
  _~>_ : (F G : ob C -> ob D) -> Set
  F ~> G  = forall {X} -> hom D (F X) (G X)

open Trans {{...}} public

-- This is used to facilitate making instances of Trans.
Trans: : (C D : Category) -> Trans C D
Trans: C D = record {}

--------------------------------------------------------------------------------
-- MonadOf
--------------------------------------------------------------------------------

record MonadOf (C : Category) (M : ob C -> ob C) : Set where
  field
    overlap {{Functor:Monad}} : FunctorOf C C M
    return : forall {X} -> hom C X (M X)
    extend : forall {X Y} -> hom C X (M Y) -> hom C (M X) (M Y)

  join : forall {X} -> hom C (M (M X)) (M X)
  join = extend id
    where instance _ = C

open MonadOf {{...}} public

Monad = MonadOf Sets

infixl 1 _>>=_ _>>_ _<=<_ _>=>_

_>>=_ : forall {M X Y} {{_ : Monad M}} -> M X -> (X -> M Y) -> M Y
_>>=_ = flip extend

_>>_ : forall {M X Y} {{_ : Monad M}} -> M X -> M Y -> M Y
x >> y = x >>= const y

_<=<_ : forall {M} {X Y Z : Set} {{_ : Monad M}}
  -> (Y -> M Z) -> (X -> M Y) -> X -> M Z
g <=< f = \ x -> f x >>= g

_>=>_ : forall {M X Y Z} {{_ : Monad M}}
  -> (X -> M Y) -> (Y -> M Z) -> X -> M Z
_>=>_ = flip _<=<_

--------------------------------------------------------------------------------
-- Applicative
--------------------------------------------------------------------------------

record Applicative (F : Set -> Set) : Set where
  infixl 24 _<*>_ _*>_ _<*_
  field
    overlap {{Functor:Applicative}} : Functor F
    _<*>_ : forall {X Y} -> F (X -> Y) -> F X -> F Y
    pure : forall {X} -> X -> F X

  _*>_ : forall {X Y} -> F X -> F Y -> F Y
  x *> y = (| (flip const) x y |)

  _<*_ : forall {X Y} -> F X -> F Y -> F X
  x <* y = (| const x y |)

open Applicative {{...}} public

-- Use this when you want to create an Applicative instance from a Monad
-- instance.
ap : forall {F X Y} {{_ : Monad F}}
  -> F (X -> Y) -> F X -> F Y
ap fs xs = do
  f <- fs
  x <- xs
  return (f x)

--------------------------------------------------------------------------------
-- Eq and Ord
--------------------------------------------------------------------------------

record Eq (X : Set) : Set where
  infix 4 _==_ _/=_
  field
    _==_ : X -> X -> Bool

  _/=_ : X -> X -> Bool
  x /= y = not (x == y)

open Eq {{...}} public

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (X : Set) : Set where
  field
    {{instance:Eq}} : Eq X
    _<_ : X -> X -> Bool

  compare : X -> X -> Ordering
  compare x y =
    if x == y then EQ else
    if x < y then LT else GT

  _<=_ : X -> X -> Bool
  x <= y = (x == y) || (x < y)

  _>_ : X -> X -> Bool
  x > y = y < x

  _>=_ : X -> X -> Bool
  x >= y = (x == y) || (x > y)

  min : X -> X -> X
  min x y = if x < y then x else y

  max : X -> X -> X
  max x y = if x > y then x else y

open Ord {{...}} public

comparing : {X Y : Set} {{_ : Ord Y}}
  -> (X -> Y) -> X -> X -> Ordering
comparing p x y = compare (p x) (p y)

--------------------------------------------------------------------------------
-- Semigroup and Monoid
--------------------------------------------------------------------------------

record Semigroup (X : Set) : Set where
  infixr 6 _<>_
  field _<>_ : X -> X -> X

open Semigroup {{...}} public

record Monoid (X : Set) : Set where
  field
    overlap {{Semigroup:Monoid}} : Semigroup X
    mempty : X

open Monoid {{...}} public

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

record Show (X : Set) : Set where
  field
    show : X -> String

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
  Append:List : forall {X} -> Append (List X) (List X) (List X)
  Append:List ._++_ [] ys = ys
  Append:List ._++_ (x :: xs) ys = x :: xs ++ ys

  Append:Vector : forall {m n X}
    -> Append (Vector X m) (Vector X n) (Vector X (m + n))
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

  Eq:Pair : forall {X Y} {{_ : Eq X}} {{_ : Eq Y}} -> Eq (Pair X Y)
  Eq:Pair ._==_ (Pair: x y) (Pair: x' y') = (x == x') && (y == y')

  Eq:Either : forall {X Y} {{_ : Eq X}} {{_ : Eq Y}} -> Eq (X + Y)
  Eq:Either ._==_ = \ where
    (left x) (left x') -> x == x'
    (right y) (right y') -> y == y'
    _ _ -> false

  Eq:Maybe : forall {X} {{_ : Eq X}} -> Eq (Maybe X)
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
  Functor:Pair : forall {X} -> Functor (Pair X)
  Functor:Pair .map f (Pair: x y) = Pair: x (f y)

  Functor:Either : forall {X} -> Functor (Either X)
  Functor:Either .map f (left x) = left x
  Functor:Either .map f (right y) = right (f y)

  Functor:Maybe : Functor Maybe
  Functor:Maybe .map f nothing = nothing
  Functor:Maybe .map f (just x) = just (f x)

  Functor:List : Functor List
  Functor:List .map f [] = []
  Functor:List .map f (x :: xs) = f x :: map f xs

--------------------------------------------------------------------------------
-- Monad instances
--------------------------------------------------------------------------------

instance
  Monad:Either : forall {X} -> Monad (Either X)
  Monad:Either .return y = right y
  Monad:Either .extend k (left x) = left x
  Monad:Either .extend k (right y) = k y

  Monad:Maybe : Monad Maybe
  Monad:Maybe .return = just
  Monad:Maybe .extend k nothing = nothing
  Monad:Maybe .extend k (just x) = k x

  Monad:List : Monad List
  Monad:List .return = [_]
  Monad:List .extend k [] = []
  Monad:List .extend k (x :: xs) = k x ++ extend k xs

--------------------------------------------------------------------------------
-- Applicative instances
--------------------------------------------------------------------------------

instance
  Applicative:Either : forall {X} -> Applicative (Either X)
  Applicative:Either = \ where
    .pure -> return
    ._<*>_ -> ap

  Applicative:Maybe : Applicative Maybe
  Applicative:Maybe = \ where
    .pure -> return
    ._<*>_ -> ap

  Applicative:List : Applicative List
  Applicative:List = \ where
    .pure -> return
    ._<*>_ -> ap

--------------------------------------------------------------------------------
-- Trans instances
--------------------------------------------------------------------------------

instance
  Endotrans:Sets = Trans: Sets Sets

--------------------------------------------------------------------------------
-- Semigroup instances
--------------------------------------------------------------------------------

instance
  Dual:Semigroup : forall {X} -> Dual (Semigroup X)
  Dual:Semigroup .Op S = let instance _ = S in \ where
    ._<>_ x y -> y <> x

  Semigroup:Void : Semigroup Void
  Semigroup:Void ._<>_ = \ ()

  Semigroup:Unit : Semigroup Unit
  Semigroup:Unit ._<>_ tt tt = tt

  Semigroup:All : Semigroup All
  Semigroup:All ._<>_ (All: x) (All: y) = All: (x && y)

  Semigroup:Any : Semigroup Any
  Semigroup:Any ._<>_ (Any: x) (Any: y) = Any: (x || y)

Semigroup:Sum : Semigroup Nat
Semigroup:Sum ._<>_ = _+_

Semigroup:Product : Semigroup Nat
Semigroup:Product ._<>_ = _*_

instance
  Semigroup:String : Semigroup String
  Semigroup:String ._<>_ = _++_

  Semigroup:List : forall {X} -> Semigroup (List X)
  Semigroup:List ._<>_ = _++_

  Semigroup:Function : {X Y : Set} {{_ : Semigroup Y}} -> Semigroup (X -> Y)
  Semigroup:Function ._<>_ f g = \ x -> f x <> g x

  Semigroup:<<< : forall {X} -> Semigroup (X -> X)
  Semigroup:<<< ._<>_ = _<<<_

  Semigroup:First : forall {X} -> Semigroup (Maybe X)
  Semigroup:First ._<>_ = \ where
    nothing _ -> nothing
    (just x) _ -> just x

--------------------------------------------------------------------------------
-- Monoid instances
--------------------------------------------------------------------------------

instance
  Dual:Monoid : forall {X} -> Dual (Monoid X)
  Dual:Monoid .Op M = let instance inst = M in \ where
    .Semigroup:Monoid -> Op (Semigroup:Monoid {{inst}})
    .mempty -> mempty

  Monoid:Unit : Monoid Unit
  Monoid:Unit .mempty = tt

  Monoid:All : Monoid All
  Monoid:All .mempty = All: true

  Monoid:Any : Monoid Any
  Monoid:Any .mempty = Any: false

Monoid:Sum : Monoid Nat
Monoid:Sum  = \ where
  .Semigroup:Monoid -> Semigroup:Sum
  .mempty -> 0

Monoid:Product : Monoid Nat
Monoid:Product = \ where
  .Semigroup:Monoid -> Semigroup:Product
  .mempty -> 1

instance
  Monoid:String : Monoid String
  Monoid:String .mempty = ""

  Monoid:List : forall {X} -> Monoid (List X)
  Monoid:List .mempty = []

  Monoid:Function : {X Y : Set} {{_ : Monoid Y}} -> Monoid (X -> Y)
  Monoid:Function .mempty = const mempty

  Monoid:<<< : forall {X} -> Monoid (X -> X)
  Monoid:<<< = \ where
    .Semigroup:Monoid -> Semigroup:<<<
    .mempty -> id

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

  Show:Pair : forall {X Y} {{_ : Show X}} {{_ : Show Y}} -> Show (X * Y)
  Show:Pair .show (Pair: x y) = "Pair: " ++ show x ++ " " ++ show y

  Show:Either : forall {X Y} {{_ : Show X}} {{_ : Show Y}} -> Show (X + Y)
  Show:Either .show = \ where
    (left x) -> "left " ++ show x
    (right y) -> "right " ++ show y

  Show:Maybe : {X : Set} {{_ : Show X}} -> Show (Maybe X)
  Show:Maybe .show = \ where
    (just x) -> "just " ++ show x
    nothing -> "nothing"

  Show:List : forall {X} {{_ : Show X}} -> Show (List X)
  Show:List .show = \ { [] -> "[]"; xs -> "[ " ++ csv xs ++ " ]" }
    where
      csv : {X : Set} {{_ : Show X}} -> List X -> String
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
  mapIO : {X Y : Set} -> (X -> Y) -> IO X -> IO Y
  returnIO : {X : Set} -> X -> IO X
  bindIO : {X Y : Set} -> IO X -> (X -> IO Y) -> IO Y
  putStr : String -> IO Unit
  putStrLn : String -> IO Unit
  getLine : IO String
  getContents : IO String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC mapIO = \ _ _ f -> map f #-}
{-# COMPILE GHC returnIO = \ _ a -> return a #-}
{-# COMPILE GHC bindIO = \ _ _ ma f -> ma >>= f #-}
{-# COMPILE GHC putStr = Text.putStr #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC getContents = Text.getContents #-}

instance
  Functor:IO : Functor IO
  Functor:IO .map = mapIO

  Monad:IO : Monad IO
  Monad:IO .return = returnIO
  Monad:IO .extend = flip bindIO

  Applicative:IO : Applicative IO
  Applicative:IO = \ where
    .pure -> return
    ._<*>_ -> ap

  Semigroup:IO : forall {X} {{_ : Semigroup X}} -> Semigroup (IO X)
  Semigroup:IO ._<>_ x y = (| _<>_ x y |)

  Monoid:IO : forall {X} {{_ : Monoid X}} -> Monoid (IO X)
  Monoid:IO .mempty = return mempty

print : forall {X} {{_ : Show X}} -> X -> IO Unit
print x = putStrLn (show x)

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStr (f s)
