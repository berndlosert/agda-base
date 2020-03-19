{-# OPTIONS --type-in-type #-}

module Prelude where

--------------------------------------------------------------------------------
-- For notational convenience
--------------------------------------------------------------------------------

private
  variable
    A B C : Set
    F G : Set -> Set

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

record Identity (A : Set) : Set where
  constructor Identity:
  field
    run : A

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

flip : (A -> B -> C) -> B -> A -> C
flip f b a = f a b

id : A -> A
id a = a

_$_ : (A -> B) -> A -> B
_$_ = id

_#_ : A -> (A -> B) -> B
_#_ = flip _$_

_<<<_ : (B -> C) -> (A -> B) -> A -> C
g <<< f = \ a -> g (f a)

_>>>_ : (A -> B) -> (B -> C) -> A -> C
_>>>_ = flip _<<<_

const : A -> B -> A
const a _ = a

uncurry : (A -> B -> C) -> A * B -> C
uncurry f (Pair: a b) = f a b

curry : (A * B -> C) -> A -> B -> C
curry f a b = f (Pair: a b)

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
    map : (A -> B) -> (F A -> F B)

open Functor {{...}} public

infixl 24 _<$>_

_<$>_ : {{_ : Functor F}} -> (A -> B) -> F A -> F B
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
    overlap {{Applicative:Monad}} : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B

  return : A -> M A
  return = pure

  _=<<_ : (A -> M B) -> M A -> M B
  _=<<_ = flip _>>=_

  join : M (M A) -> M A
  join = _=<<_ id

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

pattern [_] a =
  a :: []
pattern [_,_] a b =
  a :: b :: []
pattern [_,_,_] a b c =
  a :: b :: c :: []
pattern [_,_,_,_] a b c d =
  a :: b :: c :: d :: []
pattern [_,_,_,_,_] a b c d e =
  a :: b :: c :: d :: e :: []
pattern [_,_,_,_,_,_] a b c d e f =
  a :: b :: c :: d :: e :: f :: []
pattern [_,_,_,_,_,_,_] a b c d e f g =
  a :: b :: c :: d :: e :: f :: g :: []
pattern [_,_,_,_,_,_,_,_] a b c d e f g h =
  a :: b :: c :: d :: e :: f :: g :: h :: []
pattern [_,_,_,_,_,_,_,_,_] a b c d e f g h i =
  a :: b :: c :: d :: e :: f :: g :: h :: i :: []
pattern [_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j =
  a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: []

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
  Eq:Char ._==_ c d = ord c == ord d

  Eq:String : Eq String
  Eq:String ._==_ = Agda.Builtin.String.primStringEquality

  Eq:Pair : {{_ : Eq A}} {{_ : Eq B}} -> Eq (Pair A B)
  Eq:Pair ._==_ (Pair: a b) (Pair: c d) = (a == c) && (b == d)

  Eq:Either : {{_ : Eq A}} {{_ : Eq B}} -> Eq (A + B)
  Eq:Either ._==_ = \ where
    (left x) (left y) -> x == y
    (right x) (right y) -> x == y
    _ _ -> false

  Eq:Maybe : {{_ : Eq A}} -> Eq (Maybe A)
  Eq:Maybe ._==_ = \ where
    nothing nothing -> true
    (just x) (just y) -> x == y
    _ _ -> false

  Eq:Identity : {{_ : Eq A}} -> Eq (Identity A)
  Eq:Identity ._==_ (Identity: x) (Identity: y) = x == y

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

  Ord:Identity : {{_ : Ord A}} -> Ord (Identity A)
  Ord:Identity ._<_ (Identity: x) (Identity: y) = x < y

--------------------------------------------------------------------------------
-- Functor instances
--------------------------------------------------------------------------------

instance
  Functor:Pair : Functor (A *_)
  Functor:Pair .map f (Pair: a x) = Pair: a (f x)

  Functor:Either : Functor (A +_)
  Functor:Either .map f = \ where
    (left a) -> left a
    (right x) -> right (f x)

  Functor:Maybe : Functor Maybe
  Functor:Maybe .map f = \ where
    nothing -> nothing
    (just a) -> just (f a)

  Functor:List : Functor List
  Functor:List .map f [] = []
  Functor:List .map f (x :: xs) = f x :: map f xs

  Functor:Identity : Functor Identity
  Functor:Identity .map f (Identity: a) = Identity: (f a)

--------------------------------------------------------------------------------
-- Applicative instances
--------------------------------------------------------------------------------

instance
  Applicative:Either : Applicative (A +_)
  Applicative:Either = \ where
    .pure -> right
    ._<*>_ (left a) _ -> left a
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

  Applicative:Identity : Applicative Identity
  Applicative:Identity = \ where
    .pure -> Identity:
    ._<*>_ (Identity: f) x -> map f x

--------------------------------------------------------------------------------
-- Monad instances
--------------------------------------------------------------------------------

instance
  Monad:Either : Monad (A +_)
  Monad:Either ._>>=_ = \ where
    (left a) k -> left a
    (right x) k -> k x

  Monad:Maybe : Monad Maybe
  Monad:Maybe ._>>=_ = \ where
    nothing k -> nothing
    (just x) k -> k x

  Monad:List : Monad List
  Monad:List ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x ++ (xs >>= k)

  Monad:Identity : Monad Identity
  Monad:Identity ._>>=_ (Identity: a) k = k a

--------------------------------------------------------------------------------
-- Semigroup instances
--------------------------------------------------------------------------------

instance
  Semigroup:Dual : {{_ : Semigroup A}} -> Semigroup (Dual A)
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

  Semigroup:Maybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  Semigroup:Maybe ._<>_ = \ where
    nothing m -> m
    m nothing -> m
    (just x) (just y) -> just (x <> y)

  Semigroup:List : Semigroup (List A)
  Semigroup:List ._<>_ = _++_

  Semigroup:Function : {{_ : Semigroup B}} -> Semigroup (A -> B)
  Semigroup:Function ._<>_ f g = \ a -> f a <> g a

  Semigroup:<<< : Semigroup (A -> A)
  Semigroup:<<< ._<>_ = _<<<_

  Semigroup:First : Semigroup (First A)
  Semigroup:First ._<>_ x _ = x

--------------------------------------------------------------------------------
-- Monoid instances
--------------------------------------------------------------------------------

instance
  Monoid:Dual : {{_ : Monoid A}} -> Monoid (Dual A)
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

  Monoid:Maybe : {{_ : Monoid A}} -> Monoid (Maybe A)
  Monoid:Maybe .mempty = nothing

  Monoid:List : Monoid (List A)
  Monoid:List .mempty = []

  Monoid:Function : {{_ : Monoid B}} -> Monoid (A -> B)
  Monoid:Function .mempty = const mempty

  Monoid:<<< : Monoid (A -> A)
  Monoid:<<< = \ where
    .Semigroup:Monoid -> Semigroup:<<<
    .mempty -> id

  Monoid:First : Monoid (First A)
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

  Show:Pair : {{_ : Show A}} {{_ : Show B}} -> Show (A * B)
  Show:Pair .show (Pair: x y) = "(" ++ show x ++ " , " ++ show y ++ ")"

  Show:Either : {{_ : Show A}} {{_ : Show B}} -> Show (A + B)
  Show:Either .show = \ where
    (left x) -> "left " ++ show x
    (right y) -> "right " ++ show y

  Show:Maybe : {{_ : Show A}} -> Show (Maybe A)
  Show:Maybe .show = \ where
    (just x) -> "just " ++ show x
    nothing -> "nothing"

  Show:List : {{_ : Show A}} -> Show (List A)
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
  Functor:IO : Functor IO
  Functor:IO .map f io = bindIO io (f >>> pureIO)

  Applicative:IO : Applicative IO
  Applicative:IO = \ where
    .pure -> pureIO
    ._<*>_ fs xs -> bindIO fs (\ f -> bindIO xs (\ x -> pureIO (f x)))

  Monad:IO : Monad IO
  Monad:IO ._>>=_ = bindIO

  Semigroup:IO : {{_ : Semigroup A}} -> Semigroup (IO A)
  Semigroup:IO ._<>_ x y = (| _<>_ x y |)

  Monoid:IO : {{_ : Monoid A}} -> Monoid (IO A)
  Monoid:IO .mempty = return mempty

print : {{_ : Show A}} -> A -> IO Unit
print x = putStrLn (show x)

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStr (f s)
