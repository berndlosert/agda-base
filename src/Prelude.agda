{-# OPTIONS --type-in-type #-}

module Prelude where

-------------------------------------------------------------------------------
-- Primitive types
-------------------------------------------------------------------------------

data Void : Set where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit)
  renaming (tt to unit)

open import Agda.Builtin.Bool public
  using (Bool)
  renaming (false to False)
  renaming (true to True)

data Ordering : Set where
  LT EQ GT : Ordering

open import Agda.Builtin.Nat public
  using (Nat)
  renaming (zero to Zero)
  renaming (suc to Suc)

open import Agda.Builtin.Int public
  using (Int)
  renaming (pos to Pos)
  renaming (negsuc to NegSuc)

open import Agda.Builtin.Float public
  using (Float)

open import Agda.Builtin.Char public
  using (Char)

open import Agda.Builtin.String public
  using (String)

open import Agda.Builtin.Equality public
  renaming (_≡_ to _===_)
  renaming (refl to Refl)

Function : Set -> Set -> Set
Function a b = a -> b

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b

{-# COMPILE GHC Either = data Either (Left | Right) #-}

open import Agda.Builtin.Sigma public
  renaming (Σ to DPair)
  renaming (_,_ to DPair:)

record Pair (a b : Set) : Set where
  constructor Pair:
  field
    fst : a
    snd : b

open Pair public

infixl 1 _,_
pattern _,_ x y = Pair: x y

{-# COMPILE GHC Pair = data (,) ((,)) #-}

open import Agda.Builtin.Maybe public
  using (Maybe)
  renaming (nothing to Nothing)
  renaming (just to Just)

open import Agda.Builtin.List public
  using (List)
  using ([])
  renaming (_∷_ to _::_)

open import Agda.Builtin.IO public
  using (IO)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c d l r s v : Set
    f m : Set -> Set
    p : Set -> Set -> Set

-------------------------------------------------------------------------------
-- Dangerous primitives
-------------------------------------------------------------------------------

record Partial : Set where
  field oops : Void

open Partial {{...}} public

postulate
  trustMe : a
  error : String -> a

undefined : {{Partial}} -> a
undefined = error "Prelude.undefined"

unsafePerform : ({{Partial}} -> a) -> a
unsafePerform x = x {{trustMe}}

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC error = \ _ s -> error (Data.Text.unpack s) #-}

-------------------------------------------------------------------------------
-- Function primitives
-------------------------------------------------------------------------------

the : (a : Set) -> a -> a
the _ x = x

const : a -> b -> a
const x _ = x

flip : (a -> b -> c) -> b -> a -> c
flip f x y = f y x

infixr 0 _$_
_$_ : (a -> b) -> a -> b
f $ x = f x

infixl 1 _#_
_#_ : a -> (a -> b) -> b
_#_ x f = f x

case_of_ : a -> (a -> b) -> b
case_of_ x f = f x

-------------------------------------------------------------------------------
-- Strictness primitives
-------------------------------------------------------------------------------

open import Agda.Builtin.Strict

infixr 0 _$!_
_$!_ : (a -> b) -> a -> b
f $! x = primForce x f

seq : a -> b -> b
seq a b = const b $! a

-------------------------------------------------------------------------------
-- Bool primitives
-------------------------------------------------------------------------------

Assert : Bool -> Set
Assert False = Void
Assert True = Unit

bool : a -> a -> Bool -> a
bool x _ False = x
bool _ x True = x

infixr 0 if_then_else_
if_then_else_ : Bool -> a -> a -> a
if b then x else y = bool y x b

not : Bool -> Bool
not False = True
not True = False

infixr 2 _||_
_||_ : Bool -> Bool -> Bool
False || x = x
True || _ = True

infixr 3 _&&_
_&&_ : Bool -> Bool -> Bool
False && _ = False
True && x = x

-------------------------------------------------------------------------------
-- Either primitives
-------------------------------------------------------------------------------

either : (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x) = f x
either f g (Right x) = g x

mirror : Either a b -> Either b a
mirror = either Right Left

fromEither : Either a a -> a
fromEither (Left x) = x
fromEither (Right x) = x

isLeft : Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight : Either a b -> Bool
isRight (Left _) = False
isRight _ = True

fromLeft : {{Partial}} -> Either a b -> a
fromLeft (Left x) = x
fromLeft _ = undefined

fromRight : {{Partial}} -> Either a b -> b
fromRight (Right x) = x
fromRight _ = undefined

-------------------------------------------------------------------------------
-- Pair primitives
-------------------------------------------------------------------------------

pair : (a -> b) -> (a -> c) -> a -> Pair b c
pair f g x = (f x , g x)

swap : Pair a b -> Pair b a
swap = pair snd fst

dup : a -> Pair a a
dup x = (x , x)

uncurry : (a -> b -> c) -> Pair a b -> c
uncurry f (x , y) = f x y

curry : (Pair a b -> c) -> a -> b -> c
curry f x y = f (x , y)

apply : Pair (a -> b) a -> b
apply (f , x) = f x

-------------------------------------------------------------------------------
-- Maybe primitives
-------------------------------------------------------------------------------

isJust : Maybe a -> Bool
isJust (Just _) = True
isJust _ = False

isNothing : Maybe a -> Bool
isNothing (Just _) = False
isNothing _ = True

fromJust : {{Partial}} -> Maybe a -> a
fromJust (Just a) = a

maybe : b -> (a -> b) -> Maybe a -> b
maybe b f Nothing = b
maybe b f (Just a) = f a

-------------------------------------------------------------------------------
-- IO primitives
-------------------------------------------------------------------------------

private
  postulate
    mapIO : (a -> b) -> IO a -> IO b
    pureIO : a -> IO a
    apIO : IO (a -> b) -> IO a -> IO b
    bindIO : IO a -> (a -> IO b) -> IO b

{-# COMPILE GHC mapIO = \ _ _ -> fmap #-}
{-# COMPILE GHC pureIO = \ _ -> pure #-}
{-# COMPILE GHC apIO = \ _ _ -> (<*>) #-}
{-# COMPILE GHC bindIO = \ _ _ -> (>>=) #-}

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

record Eq (a : Set) : Set where
  infix 4 _==_
  field _==_ : a -> a -> Bool

  infix 4 _/=_
  _/=_ : a -> a -> Bool
  x /= y = if x == y then False else True

  equating : (b -> a) -> b -> b -> Bool
  equating f x y = f x == f y

open Eq {{...}} public

instance
  Eq-Void : Eq Void
  Eq-Void ._==_ = \ ()

  Eq-Unit : Eq Unit
  Eq-Unit ._==_ unit unit = True

  Eq-Bool : Eq Bool
  Eq-Bool ._==_ = \ where
    True True -> True
    False False -> False
    _ _ -> False

  Eq-Ordering : Eq Ordering
  Eq-Ordering ._==_ = \ where
    LT LT -> True
    EQ EQ -> True
    GT GT -> True
    _ _ -> False

  Eq-Nat : Eq Nat
  Eq-Nat ._==_ = Agda.Builtin.Nat._==_

  Eq-Int : Eq Int
  Eq-Int ._==_ = \ where
    (Pos m) (Pos n) -> m == n
    (NegSuc m) (NegSuc n) -> m == n
    _ _ -> False

  Eq-Float : Eq Float
  Eq-Float ._==_ = Agda.Builtin.Float.primFloatEquality

  Eq-Char : Eq Char
  Eq-Char ._==_ = Agda.Builtin.Char.primCharEquality

  Eq-String : Eq String
  Eq-String ._==_ = Agda.Builtin.String.primStringEquality

  Eq-Either : {{Eq a}} -> {{Eq b}} -> Eq (Either a b)
  Eq-Either ._==_ = \ where
    (Left x) (Left y) -> x == y
    (Right x) (Right y) -> x == y
    _ _ -> False

  Eq-Pair : {{Eq a}} -> {{Eq b}} -> Eq (Pair a b)
  Eq-Pair ._==_ (x , y) (w , z) = (x == w) && (y == z)

  Eq-Maybe : {{Eq a}} -> Eq (Maybe a)
  Eq-Maybe ._==_ = \ where
    Nothing Nothing -> True
    (Just x) (Just y) -> x == y
    _ _ -> False

  Eq-List : {{Eq a}} -> Eq (List a)
  Eq-List ._==_ = \ where
    [] [] -> True
    (x :: xs) (y :: ys) -> x == y && xs == ys
    _ _ -> False

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

record Ord (a : Set) : Set where
  field
    overlap {{Eq-super}} : Eq a
    compare : a -> a -> Ordering

  comparing : (b -> a) -> b -> b -> Ordering
  comparing f x y = compare (f x) (f y)

  infixl 4 _<_
  _<_ : a -> a -> Bool
  x < y = case compare x y of \ where
    LT -> True
    _ -> False

  infixl 4 _>_
  _>_ : a -> a -> Bool
  _>_ = flip _<_

  infixl 4 _<=_
  _<=_ : a -> a -> Bool
  x <= y = case compare x y of \ where
    GT -> False
    _ -> True

  infixl 4 _>=_
  _>=_ : a -> a -> Bool
  _>=_ = flip _<=_

  min : a -> a -> a
  min x y = if x < y then x else y

  max : a -> a -> a
  max x y = if x < y then y else x

open Ord {{...}} public

instance
  Ord-Void : Ord Void
  Ord-Void .compare = \ ()

  Ord-Unit : Ord Unit
  Ord-Unit .compare unit unit = EQ

  Ord-Bool : Ord Bool
  Ord-Bool .compare False True = LT
  Ord-Bool .compare True False = GT
  Ord-Bool .compare _ _ = EQ

  Ord-Ordering : Ord Ordering
  Ord-Ordering .compare LT EQ = LT
  Ord-Ordering .compare LT GT = LT
  Ord-Ordering .compare EQ LT = GT
  Ord-Ordering .compare EQ GT = LT
  Ord-Ordering .compare GT LT = GT
  Ord-Ordering .compare GT EQ = GT
  Ord-Ordering .compare _ _ = EQ

  Ord-Nat : Ord Nat
  Ord-Nat .compare m n =
    if m == n then EQ
    else if Agda.Builtin.Nat._<_ m n then LT
    else GT

  Ord-Int : Ord Int
  Ord-Int .compare = \ where
    (Pos m) (Pos n) -> compare m n
    (NegSuc m) (NegSuc n) -> compare n m
    (Pos _) (NegSuc _) -> GT
    (NegSuc _) (Pos _) -> LT

  Ord-Float : Ord Float
  Ord-Float .compare x y =
    if x == y then EQ
    else if Agda.Builtin.Float.primFloatLess x y then LT
    else GT

  Ord-Char : Ord Char
  Ord-Char .compare l r =
    let ord = Agda.Builtin.Char.primCharToNat
    in compare (ord l) (ord r)

  Ord-List : {{Ord a}} -> Ord (List a)
  Ord-List .compare [] [] = EQ
  Ord-List .compare [] (x :: xs) = LT
  Ord-List .compare (x :: xs) [] = GT
  Ord-List .compare (x :: xs) (y :: ys) =
    case compare x y of \ where
      LT -> LT
      GT -> GT
      EQ -> compare xs ys

  Ord-String : Ord String
  Ord-String .compare l r =
    let unpack = Agda.Builtin.String.primStringToList
    in compare (unpack l) (unpack r)

  Ord-Pair : {{Ord a}} -> {{Ord b}} -> Ord (Pair a b)
  Ord-Pair .compare (x , y) (w , z) =
    case compare x w of \ where
      LT -> LT
      GT -> GT
      EQ -> compare y z

  Ord-Maybe : {{Ord a}} -> Ord (Maybe a)
  Ord-Maybe .compare Nothing Nothing = EQ
  Ord-Maybe .compare Nothing _ = LT
  Ord-Maybe .compare (Just x) (Just y) = compare x y
  Ord-Maybe .compare (Just _) _ = GT

-------------------------------------------------------------------------------
-- FromNat
-------------------------------------------------------------------------------

record FromNat (a : Set) : Set where
  field
    FromNatConstraint : Nat -> Set
    fromNat : (n : Nat) -> {{FromNatConstraint n}} -> a

open FromNat {{...}} public

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY FromNat.fromNat _ n = fromNat n #-}

instance
  FromNat-Nat : FromNat Nat
  FromNat-Nat .FromNatConstraint _ = Unit
  FromNat-Nat .fromNat n = n

  FromNat-Int : FromNat Int
  FromNat-Int .FromNatConstraint _ = Unit
  FromNat-Int .fromNat n = Pos n

  FromNat-Float : FromNat Float
  FromNat-Float .FromNatConstraint _ = Unit
  FromNat-Float .fromNat n = Agda.Builtin.Float.primNatToFloat n

-------------------------------------------------------------------------------
-- ToNat
-------------------------------------------------------------------------------

record ToNat (a : Set) : Set where
  field
    ToNatConstraint : a -> Set
    toNat : (x : a) -> {{ToNatConstraint x}} -> Nat

open ToNat {{...}} public

instance
  ToNat-Int : ToNat Int
  ToNat-Int .ToNatConstraint _ = Unit
  ToNat-Int .toNat (Pos n) = n
  ToNat-Int .toNat (NegSuc n) = 0

-------------------------------------------------------------------------------
-- Neg
-------------------------------------------------------------------------------

record Neg (a : Set) : Set where
  field
    NegConstraint : Nat -> Set
    neg : (n : Nat) -> {{NegConstraint n}} -> a

open Neg {{...}} public

{-# BUILTIN FROMNEG neg #-}
{-# DISPLAY Neg.neg _ n = neg n #-}

instance
  Neg-Int : Neg Int
  Neg-Int .NegConstraint _ = Unit
  Neg-Int .neg 0 = Pos 0
  Neg-Int .neg (Suc n) = NegSuc n

  Neg-Float : Neg Float
  Neg-Float .NegConstraint _ = Unit
  Neg-Float .neg n =
    Agda.Builtin.Float.primFloatNegate (Agda.Builtin.Float.primNatToFloat n)

-------------------------------------------------------------------------------
-- Num
-------------------------------------------------------------------------------

record Num (a : Set) : Set where
  infixl 6 _+_
  infixl 6 _-_
  infixl 7 _*_
  field
    {{FromNat-super}} : FromNat a
    {{Ord-super}} : Ord a
    {{HasZero}} : FromNatConstraint {{FromNat-super}} 0
    {{HasOne}} : FromNatConstraint {{FromNat-super}} 1
    _+_ : a -> a -> a
    _-_ : a -> a -> a
    _*_ : a -> a -> a

  times : Nat -> a -> a
  times 0 _ = 0
  times (Suc n) x = times n x + x

  infixr 8 _^_
  _^_ : a -> Nat -> a
  a ^ 0 = 1
  a ^ (Suc n) = a ^ n * a

open Num {{...}} public

instance
  Num-Nat : Num Nat
  Num-Nat ._+_ = Agda.Builtin.Nat._+_
  Num-Nat ._-_ = Agda.Builtin.Nat._-_
  Num-Nat ._*_ = Agda.Builtin.Nat._*_

  Num-Int : Num Int
  Num-Int ._+_ = \ where
      (NegSuc m) (NegSuc n) -> NegSuc (Suc (m + n))
      (NegSuc m) (Pos n) -> diff n (Suc m)
      (Pos m) (NegSuc n) -> diff m (Suc n)
      (Pos m) (Pos n) -> Pos (m + n)
    where
      diff : Nat -> Nat -> Int
      diff m Zero = Pos m
      diff Zero (Suc n) = NegSuc n
      diff (Suc m) (Suc n) = diff m n
  Num-Int ._-_ = \ where
    m (Pos n) -> m + (neg n)
    m (NegSuc n) -> m + Pos (Suc n)
  Num-Int ._*_ = \ where
    (Pos n) (Pos m) -> Pos (n * m)
    (NegSuc n) (NegSuc m) -> Pos (Suc n * Suc m)
    (Pos n) (NegSuc m) -> neg (n * Suc m)
    (NegSuc n) (Pos m) -> neg (Suc n * m)

  Num-Float : Num Float
  Num-Float ._+_ = Agda.Builtin.Float.primFloatPlus
  Num-Float ._-_ = Agda.Builtin.Float.primFloatMinus
  Num-Float ._*_ = Agda.Builtin.Float.primFloatTimes

-------------------------------------------------------------------------------
-- Signed
-------------------------------------------------------------------------------

record Signed (a : Set) : Set where
  field
    overlap {{Num-super}} : Num a
    overlap {{Neg-super}} : Neg a
    -_ : a -> a
    abs : a -> a
    signum : a -> a

open Signed {{...}} public

instance
  Signed-Int : Signed Int
  Signed-Int .-_ = \ where
    (Pos 0) -> Pos 0
    (Pos (Suc n)) -> NegSuc n
    (NegSuc n) -> Pos (Suc n)
  Signed-Int .abs n@(Pos _) = n
  Signed-Int .abs (NegSuc n) = Pos (Suc n)
  Signed-Int .signum n@(Pos 0) = n
  Signed-Int .signum (Pos _) = Pos 1
  Signed-Int .signum (NegSuc _) = NegSuc 0

  Signed-Float : Signed Float
  Signed-Float .-_ = Agda.Builtin.Float.primFloatNegate
  Signed-Float .abs x = if x < 0.0 then - x else x
  Signed-Float .signum x = case compare x 0.0 of \ where
    LT -> -1.0
    EQ -> 0.0
    GT -> 1.0

-------------------------------------------------------------------------------
-- Integral
-------------------------------------------------------------------------------

record Integral (a : Set) : Set where
  field
    overlap {{Num-super}} : Num a
    quot : {{Partial}} -> a -> a -> a
    rem : {{Partial}} -> a -> a -> a

open Integral {{...}} public

instance
  Integral-Nat : Integral Nat
  Integral-Nat .quot m (Suc n) = Agda.Builtin.Nat.div-helper 0 n m n
  Integral-Nat .quot m 0 = undefined
  Integral-Nat .rem m (Suc n) = Agda.Builtin.Nat.mod-helper 0 n m n
  Integral-Nat .rem m 0 = undefined

  Integral-Int : Integral Int
  Integral-Int .quot = \ where
    (Pos m) (Pos n@(Suc _)) -> Pos (quot m n)
    (Pos m) (NegSuc n) -> neg (quot m (Suc n))
    (NegSuc m) (Pos n@(Suc _)) -> neg (quot (Suc m) n)
    (NegSuc m) (NegSuc n) -> Pos (quot (Suc m) (Suc n))
    _ _ -> undefined
  Integral-Int .rem = \ where
    (Pos m) (Pos n@(Suc _)) -> Pos (rem m n)
    (Pos m) (NegSuc n) -> Pos (rem m (Suc n))
    (NegSuc m) (Pos n@(Suc _)) -> neg (rem (Suc m) n)
    (NegSuc m) (NegSuc n) -> neg (rem (Suc m) (Suc n))
    _ _ -> undefined

-------------------------------------------------------------------------------
-- Fractional
-------------------------------------------------------------------------------

record Fractional (a : Set) : Set where
  field
    overlap {{Num-super}} : Num a
    _/_ : {{Partial}} -> a -> a -> a

open Fractional {{...}} public

instance
  Fractional-Float : Fractional Float
  Fractional-Float ._/_ x y = Agda.Builtin.Float.primFloatDiv x y

-------------------------------------------------------------------------------
-- Semigroup
-------------------------------------------------------------------------------

record Semigroup (a : Set) : Set where
  infixr 5 _<>_
  field _<>_ : a -> a -> a

open Semigroup {{...}} public

instance
  Semigroup-Void : Semigroup Void
  Semigroup-Void ._<>_ = \ ()

  Semigroup-Unit : Semigroup Unit
  Semigroup-Unit ._<>_ unit unit = unit

  Semigroup-Ordering : Semigroup Ordering
  Semigroup-Ordering ._<>_ = \ where
    LT _ -> LT
    EQ y -> y
    GT _ -> GT

  Semigroup-String : Semigroup String
  Semigroup-String ._<>_ = Agda.Builtin.String.primStringAppend

  Semigroup-Function : {{Semigroup b}} -> Semigroup (a -> b)
  Semigroup-Function ._<>_ f g = \ x -> f x <> g x

  Semigroup-Either : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Either a b)
  Semigroup-Either ._<>_ (Left _) x = x
  Semigroup-Either ._<>_ x _ = x

  Semigroup-Pair : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Pair a b)
  Semigroup-Pair ._<>_ (x , y) (w , z) = (x <> w , y <> z)

  Semigroup-Maybe : {{Semigroup a}} -> Semigroup (Maybe a)
  Semigroup-Maybe ._<>_ = \ where
    Nothing x -> x
    x Nothing -> x
    (Just x) (Just y) -> Just (x <> y)

  Semigroup-List : Semigroup (List a)
  Semigroup-List ._<>_ = \ where
    [] ys -> ys
    (x :: xs) ys -> x :: (xs <> ys)

  Semigroup-IO : {{Semigroup a}} -> Semigroup (IO a)
  Semigroup-IO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Set) : Set where
  field
    overlap {{Semigroup-super}} : Semigroup a
    neutral : a

open Monoid {{...}} public

instance
  Monoid-Unit : Monoid Unit
  Monoid-Unit .neutral = unit

  Monoid-Ordering : Monoid Ordering
  Monoid-Ordering .neutral = EQ

  Monoid-String : Monoid String
  Monoid-String .neutral = ""

  Monoid-Function : {{Monoid b}} -> Monoid (a -> b)
  Monoid-Function .neutral = const neutral

  Monoid-Pair : {{Monoid a}} -> {{Monoid b}} -> Monoid (Pair a b)
  Monoid-Pair .neutral = (neutral , neutral)

  Monoid-Maybe : {{Semigroup a}} -> Monoid (Maybe a)
  Monoid-Maybe .neutral = Nothing

  Monoid-List : Monoid (List a)
  Monoid-List .neutral = []

  Monoid-IO : {{Monoid a}} -> Monoid (IO a)
  Monoid-IO .neutral = pureIO neutral

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

record Category (p : Set -> Set -> Set) : Set where
  infixr 9 _<<<_
  field
    _<<<_ : p b c -> p a b -> p a c
    id : p a a

  infixr 9 _>>>_
  _>>>_ : p a b -> p b c -> p a c
  _>>>_ = flip _<<<_

open Category {{...}} public

instance
  Category-Function : Category Function
  Category-Function ._<<<_ f g x = f (g x)
  Category-Function .id x = x

-------------------------------------------------------------------------------
-- Functor
-------------------------------------------------------------------------------

record Functor (f : Set -> Set) : Set where
  field map : (a -> b) -> f a -> f b

  infixl 4 _<$>_
  _<$>_ : (a -> b) -> f a -> f b
  _<$>_ = map

  infixl 1 _<#>_
  _<#>_ : f a -> (a -> b) -> f b
  _<#>_ = flip map

  infixl 4 _<$_
  _<$_ : b -> f a -> f b
  _<$_ = map <<< const

  infixl 4 _$>_
  _$>_ : f a -> b -> f b
  _$>_ = flip _<$_

  ignore : f a -> f Unit
  ignore = unit <$_

  vacuous : f Void -> f a
  vacuous = map \ ()

open Functor {{...}} public

instance
  Functor-Function : Functor (Function a)
  Functor-Function .map = _<<<_

  Functor-Either : Functor (Either a)
  Functor-Either .map f = either Left (Right <<< f)

  Functor-Pair : Functor (Pair a)
  Functor-Pair .map f (x , y) = (x , f y)

  Functor-Maybe : Functor Maybe
  Functor-Maybe .map f = maybe Nothing (Just <<< f)

  Functor-List : Functor List
  Functor-List .map f = \ where
    [] -> []
    (x :: xs) -> f x :: map f xs

  Functor-IO : Functor IO
  Functor-IO .map = mapIO

-------------------------------------------------------------------------------
-- Contravariant
-------------------------------------------------------------------------------

record Contravariant (f : Set -> Set) : Set where
  field cmap : (a -> b) -> f b -> f a

  phantom : {{Functor f}} -> f a -> f b
  phantom x = cmap (const unit) (map (const unit) x)

open Contravariant {{...}} public

-------------------------------------------------------------------------------
-- Bifunctor
-------------------------------------------------------------------------------

record Bifunctor (p : Set -> Set -> Set) : Set where
  field
    overlap {{Functor-super}} : Functor (p a)
    lmap : (a -> b) -> p a c -> p b c

  bimap : (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = lmap f <<< map g

open Bifunctor {{...}} public

instance
  Bifunctor-Either : Bifunctor Either
  Bifunctor-Either .lmap f = either (Left <<< f) Right

  Bifunctor-Pair : Bifunctor Pair
  Bifunctor-Pair .lmap f (x , y) = (f x , y)

-------------------------------------------------------------------------------
-- Profunctor
-------------------------------------------------------------------------------

record Profunctor (p : Set -> Set -> Set) : Set where
  field
    overlap {{Functor-super}} : Functor (p a)
    lcmap : (b -> a) -> p a c -> p b c

  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lcmap f <<< map g

  arr : {{Category p}} -> (a -> b) -> p a b
  arr f = map f id

open Profunctor {{...}} public

instance
  Profunctor-Function : Profunctor Function
  Profunctor-Function .lcmap = _>>>_

-------------------------------------------------------------------------------
-- Applicative
-------------------------------------------------------------------------------

record Applicative (f : Set -> Set) : Set where
  infixl 4 _<*>_
  field
    overlap {{Functor-super}} : Functor f
    _<*>_ : f (a -> b) -> f a -> f b
    pure : a -> f a

  infixl 4 _<**>_
  _<**>_ : f a -> f (a -> b) -> f b
  xs <**> fs = (| _#_ xs fs |)

  infixl 4 _*>_
  _*>_ : f a -> f b -> f b
  a *> b = (| (flip const) a b |)

  infixl 4 _<*_
  _<*_ : f a -> f b -> f a
  a <* b = (| const a b |)

  replicateA! : Nat -> f a -> f Unit
  replicateA! n0 fa = loop n0
    where
      loop : Nat -> f Unit
      loop 0 = pure unit
      loop (Suc n) = fa *> loop n

  when : Bool -> f Unit -> f Unit
  when p x = if p then x else pure unit

  unless : Bool -> f Unit -> f Unit
  unless p x = if p then pure unit else x

open Applicative {{...}} public

{-# NON_TERMINATING #-}
forever : {{Applicative f}} -> f a -> f b
forever as = as *> forever as

instance
  Applicative-Function : Applicative (Function a)
  Applicative-Function .pure = const
  Applicative-Function ._<*>_ f g = \ x -> f x (g x)

  Applicative-Either : Applicative (Either a)
  Applicative-Either .pure = Right
  Applicative-Either ._<*>_ = \ where
    (Left a) _ -> Left a
    (Right f) -> map f

  Applicative-Pair : {{Monoid a}} -> Applicative (Pair a)
  Applicative-Pair .pure = (neutral ,_)
  Applicative-Pair ._<*>_ (u , f) (v , x) = (u <> v , f x)

  Applicative-Maybe : Applicative Maybe
  Applicative-Maybe .pure = Just
  Applicative-Maybe ._<*>_ = \ where
    (Just f) -> map f
    Nothing _ -> Nothing

  Applicative-List : Applicative List
  Applicative-List .pure = _:: []
  Applicative-List ._<*>_ = \ where
    [] _ -> []
    (f :: fs) xs -> (map f xs) <> (fs <*> xs)

  Applicative-IO : Applicative IO
  Applicative-IO .pure = pureIO
  Applicative-IO ._<*>_ = apIO

--------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

record Monad (m : Set -> Set) : Set where
  infixl 1 _>>=_
  field
    overlap {{Applicative-super}} : Applicative m
    _>>=_ : m a -> (a -> m b) -> m b

  infixl 1 _=<<_
  _=<<_ : (a -> m b) -> m a -> m b
  _=<<_ = flip _>>=_

  infixl 4 _>>_
  _>>_ : m a -> m b -> m b
  _>>_ = _*>_

  infixr 1 _<=<_
  _<=<_ : (b -> m c) -> (a -> m b) -> a -> m c
  _<=<_ f g x = g x >>= f

  infixr 1 _>=>_
  _>=>_ : (a -> m b) -> (b -> m c) -> a -> m c
  _>=>_ = flip _<=<_

  join : m (m a) -> m a
  join = _>>= id

open Monad {{...}} public

instance
  Monad-Function : Monad (Function a)
  Monad-Function ._>>=_ m k = \ a -> k (m a) a

  Monad-Either : Monad (Either a)
  Monad-Either ._>>=_ = \ where
    (Left a) _ -> Left a
    (Right x) k -> k x

  Monad-Pair : {{Monoid a}} -> Monad (Pair a)
  Monad-Pair ._>>=_ (u , x) k = let (v , y) = k x in (u <> v , y)

  Monad-Maybe : Monad Maybe
  Monad-Maybe ._>>=_ = \ where
    Nothing _ -> Nothing
    (Just x) k -> k x

  Monad-List : Monad List
  Monad-List ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x <> (xs >>= k)

  Monad-IO : Monad IO
  Monad-IO ._>>=_ = bindIO
