module Prelude where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

import Agda.Primitive as Primitive
import Agda.Builtin.Unit as Unit
import Agda.Builtin.Bool as Bool
import Agda.Builtin.Nat as Nat
import Agda.Builtin.Int as Int
import Agda.Builtin.Float as Float
import Agda.Builtin.Char as Char
import Agda.Builtin.String as String
import Agda.Builtin.Equality as Equality
import Agda.Builtin.Sigma as Sigma
import Agda.Builtin.Maybe as Maybe
import Agda.Builtin.List as List
import Agda.Builtin.IO as IO
import Agda.Builtin.Strict as Strict
import Agda.Builtin.Coinduction as Coinduction

-------------------------------------------------------------------------------
-- Primitive types
-------------------------------------------------------------------------------

open Primitive public
  using (Level)
  using (lzero)
  using (lsuc)
  renaming (_⊔_ to _lmax_)

data Void : Set where

open Unit public
  renaming (⊤ to Unit)
  using (tt)

open Bool public
  using (Bool)
  using (false)
  using (true)

data Ordering : Set where
  LT EQ GT : Ordering

{-# COMPILE GHC Ordering = data Ordering (LT | EQ | GT) #-}

open Nat public
  using (Nat)
  using (zero)
  using (suc)

open Int public
  using (Int)
  using (pos)
  using (negsuc)

open Float public
  using (Float)

open Char public
  using (Char)

open String public
  using (String)

open Equality public
  renaming (_≡_ to _===_)
  using (refl)

Function : Set -> Set -> Set
Function a b = a -> b

data Either (a b : Set) : Set where
  left : a -> Either a b
  right : b -> Either a b

{-# COMPILE GHC Either = data Either (Left | Right) #-}

open Sigma public
  renaming (Σ to DPair)
  renaming (_,_ to asDPair)

infixl 1 _,_
record Pair (a b : Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b

open Pair public

{-# COMPILE GHC Pair = data (,) ((,)) #-}

open Maybe public
  using (Maybe)
  using (nothing)
  using (just)

open List public
  using (List)
  using ([])
  renaming (_∷_ to _::_)

open IO public
  using (IO)

open Coinduction public
  renaming (∞ to Inf)
  renaming (♯_ to sharp)
  renaming (♭ to flat)

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

postulate
  trustMe : a
  panic : String -> a

undefined : a
undefined = panic "Prelude.undefined"

fromJust : Maybe a -> a
fromJust (just x) = x
fromJust nothing = panic "Prelude.fromJust: nothing"

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC panic = \ _ s -> error (Data.Text.unpack s) #-}

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

_on_ : (b -> b -> c) -> (a -> b) -> a -> a -> c
f on g = \ x y -> f (g x) (g y)

fix : (a -> a) -> a
fix f = f (fix f)

absurd : Void -> a
absurd = \ ()

applyN : Nat -> (a -> a) -> a -> a
applyN 0 _ x = x
applyN (suc n) f x = f (applyN n f x)

uncurry : (a -> b -> c) -> Pair a b -> c
uncurry f (x , y) = f x y

curry : (Pair a b -> c) -> a -> b -> c
curry f x y = f (x , y)

apply : Pair (a -> b) a -> b
apply (f , x) = f x

-------------------------------------------------------------------------------
-- Strictness primitives
-------------------------------------------------------------------------------

infixr 0 _$!_
_$!_ : (a -> b) -> a -> b
f $! x = Strict.primForce x f

infixr 9 _seq_
_seq_ : a -> b -> b
x seq y = const y $! x

-------------------------------------------------------------------------------
-- Bool primitives
-------------------------------------------------------------------------------

Assert : Bool -> Set
Assert false = Void
Assert true = Unit

infixr 0 if_then_else_
if_then_else_ : Bool -> a -> a -> a
if true then x else _ = x
if false then _ else x = x

record Boolean (a : Set) : Set where
  infixr 2 _||_
  infixr 3 _&&_
  field
    not : a -> a
    _||_ : a -> a -> a
    _&&_ : a -> a -> a

open Boolean {{...}} public

instance
  Boolean-Bool : Boolean Bool
  Boolean-Bool .not false = true
  Boolean-Bool .not true = false
  Boolean-Bool ._||_ false x = x
  Boolean-Bool ._||_ true _ = true
  Boolean-Bool ._&&_ false _ = false
  Boolean-Bool ._&&_ true x = x

  Boolean-Function : Boolean (a -> Bool)
  Boolean-Function .not f x = not (f x)
  Boolean-Function ._||_ f g x = f x || g x
  Boolean-Function ._&&_ f g x = f x && g x

------------------------------------------------------------------------------
-- Either primitives
-------------------------------------------------------------------------------

either : (a -> c) -> (b -> c) -> Either a b -> c
either f g (left x) = f x
either f g (right x) = g x

mirror : Either a b -> Either b a
mirror = either right left

fromEither : Either a a -> a
fromEither (left x) = x
fromEither (right x) = x

isLeft : Either a b -> Bool
isLeft (left _) = true
isLeft _ = false

isRight : Either a b -> Bool
isRight (left _) = false
isRight _ = true

fromLeft : a -> Either a b -> a
fromLeft _ (left x) = x
fromLeft x _ = x

fromRight : b -> Either a b -> b
fromRight _ (right x) = x
fromRight x _ = x

-------------------------------------------------------------------------------
-- Pair primitives
-------------------------------------------------------------------------------

pair : (a -> b) -> (a -> c) -> a -> Pair b c
pair f g x = (f x , g x)

swap : Pair a b -> Pair b a
swap = pair snd fst

dup : a -> Pair a a
dup x = (x , x)

-------------------------------------------------------------------------------
-- Maybe primitives
-------------------------------------------------------------------------------

isJust : Maybe a -> Bool
isJust (just _) = true
isJust _ = false

isNothing : Maybe a -> Bool
isNothing (just _) = false
isNothing _ = true

maybe : b -> (a -> b) -> Maybe a -> b
maybe x f nothing = x
maybe x f (just y) = f y

fromMaybe : a -> Maybe a -> a
fromMaybe x nothing = x
fromMaybe _ (just x) = x

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
  x /= y = if x == y then false else true

open Eq {{...}} public

instance
  Eq-Void : Eq Void
  Eq-Void ._==_ = \ ()

  Eq-Unit : Eq Unit
  Eq-Unit ._==_ tt tt = true

  Eq-Bool : Eq Bool
  Eq-Bool ._==_ = \ where
    true true -> true
    false false -> false
    _ _ -> false

  Eq-Ordering : Eq Ordering
  Eq-Ordering ._==_ = \ where
    LT LT -> true
    EQ EQ -> true
    GT GT -> true
    _ _ -> false

  Eq-Nat : Eq Nat
  Eq-Nat ._==_ = Nat._==_

  Eq-Int : Eq Int
  Eq-Int ._==_ = \ where
    (pos m) (pos n) -> m == n
    (negsuc m) (negsuc n) -> m == n
    _ _ -> false

  Eq-Float : Eq Float
  Eq-Float ._==_ = Float.primFloatEquality

  Eq-Char : Eq Char
  Eq-Char ._==_ = Char.primCharEquality

  Eq-String : Eq String
  Eq-String ._==_ = String.primStringEquality

  Eq-Either : {{Eq a}} -> {{Eq b}} -> Eq (Either a b)
  Eq-Either ._==_ = \ where
    (left x) (left y) -> x == y
    (right x) (right y) -> x == y
    _ _ -> false

  Eq-Pair : {{Eq a}} -> {{Eq b}} -> Eq (Pair a b)
  Eq-Pair ._==_ (x , y) (w , z) = (x == w) && (y == z)

  Eq-Maybe : {{Eq a}} -> Eq (Maybe a)
  Eq-Maybe ._==_ = \ where
    nothing nothing -> true
    (just x) (just y) -> x == y
    _ _ -> false

  Eq-List : {{Eq a}} -> Eq (List a)
  Eq-List ._==_ = \ where
    [] [] -> true
    (x :: xs) (y :: ys) -> x == y && xs == ys
    _ _ -> false

-------------------------------------------------------------------------------
-- Ord
-------------------------------------------------------------------------------

record Ord (a : Set) : Set where
  infixl 4 _<_
  field
    overlap {{Eq-super}} : Eq a
    _<_ : a -> a -> Bool

  infixl 4 _>_
  _>_ : a -> a -> Bool
  _>_ = flip _<_

  infixl 4 _<=_
  _<=_ : a -> a -> Bool
  x <= y = x == y || x < y

  infixl 4 _>=_
  _>=_ : a -> a -> Bool
  _>=_ = flip _<=_

  min : a -> a -> a
  min x y = if x < y then x else y

  max : a -> a -> a
  max x y = if x < y then y else x

  compare : a -> a -> Ordering
  compare x y = if x == y then EQ else if x < y then LT else GT

open Ord {{...}} public

instance
  Ord-Void : Ord Void
  Ord-Void ._<_ = \ ()

  Ord-Unit : Ord Unit
  Ord-Unit ._<_ _ _ = false

  Ord-Bool : Ord Bool
  Ord-Bool ._<_ false true = true
  Ord-Bool ._<_ _ _ = false

  Ord-Ordering : Ord Ordering
  Ord-Ordering ._<_ LT EQ = true
  Ord-Ordering ._<_ LT GT = true
  Ord-Ordering ._<_ EQ GT = true
  Ord-Ordering ._<_ _ _ = false

  Ord-Nat : Ord Nat
  Ord-Nat ._<_ = Nat._<_

  Ord-Int : Ord Int
  Ord-Int ._<_ = \ where
    (pos m) (pos n) -> m < n
    (negsuc m) (negsuc n) -> n < m
    (negsuc _) (pos _) -> true
    _ _ -> false

  Ord-Float : Ord Float
  Ord-Float ._<_ = Float.primFloatLess

  Ord-Char : Ord Char
  Ord-Char ._<_ = _<_ on Char.primCharToNat

  Ord-List : {{Ord a}} -> Ord (List a)
  Ord-List ._<_ [] [] = false
  Ord-List ._<_ [] (_ :: _) = true
  Ord-List ._<_ (_ :: _) [] = false
  Ord-List ._<_ (x :: xs) (y :: ys) = x < y && xs < ys

  Ord-String : Ord String
  Ord-String ._<_ = _<_ on String.primStringToList

  Ord-Pair : {{Ord a}} -> {{Ord b}} -> Ord (Pair a b)
  Ord-Pair ._<_ (x , y) (w , z) =
    if x < w then true else if x == w then y < z else false

  Ord-Maybe : {{Ord a}} -> Ord (Maybe a)
  Ord-Maybe ._<_ nothing (just _) = true
  Ord-Maybe ._<_ (just x) (just y) = x < y
  Ord-Maybe ._<_ _ _ = false

-------------------------------------------------------------------------------
-- FromNat
-------------------------------------------------------------------------------

record FromNat (a : Set) : Set where
  field fromNat : Nat -> a

open FromNat {{...}} public

{-# BUILTIN FROMNAT fromNat #-}

instance
  FromNat-Level : FromNat Level
  FromNat-Level .fromNat 0 = lzero
  FromNat-Level .fromNat (suc n) = lsuc (fromNat n)

  FromNat-Nat : FromNat Nat
  FromNat-Nat .fromNat n = n

  FromNat-Int : FromNat Int
  FromNat-Int .fromNat n = pos n

  FromNat-Float : FromNat Float
  FromNat-Float .fromNat n = Float.primNatToFloat n

-------------------------------------------------------------------------------
-- ToNat
-------------------------------------------------------------------------------

record ToNat (a : Set) : Set where
  field toNat : a -> Nat

open ToNat {{...}} public

instance
  ToNat-Int : ToNat Int
  ToNat-Int .toNat (pos n) = n
  ToNat-Int .toNat (negsuc n) = 0

-------------------------------------------------------------------------------
-- FromNeg
-------------------------------------------------------------------------------

record FromNeg (a : Set) : Set where
  field neg : Nat -> a

open FromNeg {{...}} public

{-# BUILTIN FROMNEG neg #-}

instance
  FromNeg-Int : FromNeg Int
  FromNeg-Int .neg 0 = pos 0
  FromNeg-Int .neg (suc n) = negsuc n

  FromNeg-Float : FromNeg Float
  FromNeg-Float .neg n =
    Float.primFloatNegate (Float.primNatToFloat n)

-------------------------------------------------------------------------------
-- Arithmetic operations
-------------------------------------------------------------------------------

record HasAdd (a : Set) : Set where
  infixl 6 _+_
  field _+_ : a -> a -> a

open HasAdd {{...}} public

record HasSub (a : Set) : Set where
  infixl 6 _-_
  field _-_ : a -> a -> a

open HasSub {{...}} public

record HasNeg (a : Set) : Set where
  field -_ : a -> a

open HasNeg {{...}} public

record HasMul (a : Set) : Set where
  infixl 7 _*_
  field _*_ : a -> a -> a

open HasMul {{...}} public

record HasExp (a : Set) : Set where
  infixr 8 _^_
  field
    Power : Set
    _^_ : a -> Power -> a

open HasExp {{...}} public

record HasDiv (a : Set) : Set where
  infixl 7 _/_
  field _/_ : a -> a -> a

open HasDiv {{...}} public

record HasMod (a : Set) : Set where
  infixl 7 _%_
  field _%_ : a -> a -> a

open HasMod {{...}} public

instance
  HasAdd-Nat : HasAdd Nat
  HasAdd-Nat ._+_ = Nat._+_

  HasSub-Nat : HasSub Nat
  HasSub-Nat ._-_ = Nat._-_

  HasMul-Nat : HasMul Nat
  HasMul-Nat ._*_ = Nat._*_

  HasExp-Nat : HasExp Nat
  HasExp-Nat .Power = Nat
  HasExp-Nat ._^_ m 0 = 1
  HasExp-Nat ._^_ m (suc n) = m * m ^ n

  HasDiv-Nat : HasDiv Nat
  HasDiv-Nat ._/_ m 0 = 0
  HasDiv-Nat ._/_ m (suc n) = Nat.div-helper 0 n m n

  HasMod-Nat : HasMod Nat
  HasMod-Nat ._%_ m 0 = 0
  HasMod-Nat ._%_ m (suc n) = Nat.mod-helper 0 n m n

  HasAdd-Int : HasAdd Int
  HasAdd-Int ._+_ = \ where
      (negsuc m) (negsuc n) -> negsuc (suc (m + n))
      (negsuc m) (pos n) -> diff n (suc m)
      (pos m) (negsuc n) -> diff m (suc n)
      (pos m) (pos n) -> pos (m + n)
    where
      diff : Nat -> Nat -> Int
      diff m 0 = pos m
      diff zero (suc n) = negsuc n
      diff (suc m) (suc n) = diff m n

  HasSub-Int : HasSub Int
  HasSub-Int ._-_ = \ where
    m (pos n) -> m + (neg n)
    m (negsuc n) -> m + pos (suc n)

  HasNeg-Int : HasNeg Int
  HasNeg-Int .-_ = \ where
    (pos 0) -> pos 0
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)

  HasMul-Int : HasMul Int
  HasMul-Int ._*_ = \ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> neg (n * suc m)
    (negsuc n) (pos m) -> neg (suc n * m)

  HasExp-Int : HasExp Int
  HasExp-Int .Power = Nat
  HasExp-Int ._^_ m 0 = pos 0
  HasExp-Int ._^_ m (suc n) = m * m ^ n

  HasDiv-Int : HasDiv Int
  HasDiv-Int ._/_ = \ where
    (pos m) (pos n@(suc _)) -> pos (m / n)
    (pos m) (negsuc n) -> neg (m / suc n)
    (negsuc m) (pos n@(suc _)) -> neg (suc m / n)
    (negsuc m) (negsuc n) -> pos (suc m / suc n)
    _ (pos zero) -> pos zero

  HasMod-Int : HasMod Int
  HasMod-Int ._%_ = \ where
    (pos m) (pos n@(suc _)) -> pos (m % n)
    (pos m) (negsuc n) -> pos (m % suc n)
    (negsuc m) (pos n@(suc _)) -> neg (suc m % n)
    (negsuc m) (negsuc n) -> neg (suc m % suc n)
    _ (pos zero) -> pos zero

  HasAdd-Float : HasAdd Float
  HasAdd-Float ._+_ = Float.primFloatPlus

  HasSub-Float : HasSub Float
  HasSub-Float ._-_ = Float.primFloatMinus

  HasNeg-Float : HasNeg Float
  HasNeg-Float .-_ = Float.primFloatNegate

  HasMul-Float : HasMul Float
  HasMul-Float ._*_ = Float.primFloatTimes

  HasExp-Float : HasExp Float
  HasExp-Float .Power = Float
  HasExp-Float ._^_ = Float.primFloatPow

  HasDiv-Float : HasDiv Float
  HasDiv-Float ._/_ x y = Float.primFloatDiv x y

-------------------------------------------------------------------------------
-- Semigroup
-------------------------------------------------------------------------------

record Semigroup (a : Set) : Set where
  infixr 5 _<>_
  field _<>_ : a -> a -> a

open Semigroup {{...}} public

asSemigroup : (a -> a -> a) -> Semigroup a
asSemigroup f = \ where
  ._<>_ -> f

instance
  Semigroup-Void : Semigroup Void
  Semigroup-Void ._<>_ = \ ()

  Semigroup-Unit : Semigroup Unit
  Semigroup-Unit ._<>_ tt tt = tt

  Semigroup-Ordering : Semigroup Ordering
  Semigroup-Ordering ._<>_ = \ where
    LT _ -> LT
    EQ y -> y
    GT _ -> GT

  Semigroup-String : Semigroup String
  Semigroup-String ._<>_ = String.primStringAppend

  Semigroup-Function : {{Semigroup b}} -> Semigroup (a -> b)
  Semigroup-Function ._<>_ f g = \ x -> f x <> g x

  Semigroup-Either : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Either a b)
  Semigroup-Either ._<>_ (left _) x = x
  Semigroup-Either ._<>_ x _ = x

  Semigroup-Pair : {{Semigroup a}} -> {{Semigroup b}}
    -> Semigroup (Pair a b)
  Semigroup-Pair ._<>_ (x , y) (w , z) = (x <> w , y <> z)

  Semigroup-Maybe : {{Semigroup a}} -> Semigroup (Maybe a)
  Semigroup-Maybe ._<>_ = \ where
    nothing x -> x
    x nothing -> x
    (just x) (just y) -> just (x <> y)

  Semigroup-List : Semigroup (List a)
  Semigroup-List ._<>_ = \ where
    [] ys -> ys
    (x :: xs) ys -> x :: (xs <> ys)

  Semigroup-IO : {{Semigroup a}} -> Semigroup (IO a)
  Semigroup-IO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| x <> y |)

-------------------------------------------------------------------------------
-- Monoid
-------------------------------------------------------------------------------

record Monoid (a : Set) : Set where
  field
    overlap {{Semigroup-super}} : Semigroup a
    mempty : a

  mtimes : Nat -> a -> a
  mtimes 0 _ = mempty
  mtimes (suc n) x = x <> mtimes n x

open Monoid {{...}} public

instance
  Monoid-Unit : Monoid Unit
  Monoid-Unit .mempty = tt

  Monoid-Ordering : Monoid Ordering
  Monoid-Ordering .mempty = EQ

  Monoid-String : Monoid String
  Monoid-String .mempty = ""

  Monoid-Function : {{Monoid b}} -> Monoid (a -> b)
  Monoid-Function .mempty = const mempty

  Monoid-Pair : {{Monoid a}} -> {{Monoid b}} -> Monoid (Pair a b)
  Monoid-Pair .mempty = (mempty , mempty)

  Monoid-Maybe : {{Semigroup a}} -> Monoid (Maybe a)
  Monoid-Maybe .mempty = nothing

  Monoid-List : Monoid (List a)
  Monoid-List .mempty = []

  Monoid-IO : {{Monoid a}} -> Monoid (IO a)
  Monoid-IO .mempty = pureIO mempty

-------------------------------------------------------------------------------
-- Semigroupoid
-------------------------------------------------------------------------------

record Semigroupoid {k : Set} (p : k -> k -> Set) : Set where
  infixr 9 _<<<_
  field _<<<_ : {a b c : k} -> p b c -> p a b -> p a c

  infixr 9 _>>>_
  _>>>_ : {a b c : k} -> p a b -> p b c -> p a c
  _>>>_ = flip _<<<_

open Semigroupoid {{...}} public

instance
  Semigroupoid-Function : Semigroupoid Function
  Semigroupoid-Function ._<<<_ f g x = f (g x)

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

record Category {k : Set} (p : k -> k -> Set) : Set where
  field
    {{Semigroupoid-super}} : Semigroupoid p
    id : {a : k} -> p a a

open Category {{...}} public

instance
  Category-Function : Category Function
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
  ignore = tt <$_

  vacuous : f Void -> f a
  vacuous = map \ ()

open Functor {{...}} public

instance
  Functor-Function : Functor (Function a)
  Functor-Function .map = _<<<_

  Functor-Either : Functor (Either a)
  Functor-Either .map f = either left (right <<< f)

  Functor-Pair : Functor (Pair a)
  Functor-Pair .map f (x , y) = (x , f y)

  Functor-Maybe : Functor Maybe
  Functor-Maybe .map f = maybe nothing (just <<< f)

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
  phantom x = cmap (const tt) (map (const tt) x)

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
  Bifunctor-Either .lmap f = either (left <<< f) right

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

  infixl 4 _*>_
  _*>_ : f a -> f b -> f b
  a *> b = (| (flip const) a b |)

  infixl 4 _<*_
  _<*_ : f a -> f b -> f a
  a <* b = (| const a b |)

  replicateA* : Nat -> f a -> f Unit
  replicateA* 0 _ = pure tt
  replicateA* (suc n) x = x *> replicateA* n x

  when : Bool -> f Unit -> f Unit
  when p x = if p then x else pure tt

  unless : Bool -> f Unit -> f Unit
  unless p x = if p then pure tt else x

  forever : f a -> f b
  forever x = x *> forever x

open Applicative {{...}} public

instance
  Applicative-Function : Applicative (Function a)
  Applicative-Function .pure = const
  Applicative-Function ._<*>_ f g = \ x -> f x (g x)

  Applicative-Either : Applicative (Either a)
  Applicative-Either .pure = right
  Applicative-Either ._<*>_ = \ where
    (left a) _ -> left a
    (right f) -> map f

  Applicative-Pair : {{Monoid a}} -> Applicative (Pair a)
  Applicative-Pair .pure = (mempty ,_)
  Applicative-Pair ._<*>_ (u , f) (v , x) = (u <> v , f x)

  Applicative-Maybe : Applicative Maybe
  Applicative-Maybe .pure = just
  Applicative-Maybe ._<*>_ = \ where
    (just f) -> map f
    nothing _ -> nothing

  Applicative-List : Applicative List
  Applicative-List .pure = _:: []
  Applicative-List ._<*>_ = \ where
    [] _ -> []
    (f :: fs) xs -> (f <$> xs) <> (fs <*> xs)

  Applicative-IO : Applicative IO
  Applicative-IO .pure = pureIO
  Applicative-IO ._<*>_ = apIO

-------------------------------------------------------------------------------
-- Alternative
-------------------------------------------------------------------------------

record Alternative (f : Set -> Set) : Set where
  infixl 3 _<|>_
  field
    overlap {{Applicative-super}} : Applicative f
    _<|>_ : f a -> f a -> f a
    azero : f a

  guard : Bool -> f Unit
  guard true = pure tt
  guard false = azero

  guarded : (a -> Bool) -> a -> f a
  guarded p x = if p x then pure x else azero

open Alternative {{...}} public

instance
  Alternative-Maybe : Alternative Maybe
  Alternative-Maybe .azero = nothing
  Alternative-Maybe ._<|>_ nothing r = r
  Alternative-Maybe ._<|>_ l _ = l

  Alternative-List : Alternative List
  Alternative-List .azero = mempty
  Alternative-List ._<|>_ = _<>_

-------------------------------------------------------------------------------
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
  Monad-Function ._>>=_ f g = \ x -> g (f x) x

  Monad-Either : Monad (Either a)
  Monad-Either ._>>=_ = \ where
    (left a) _ -> left a
    (right x) k -> k x

  Monad-Pair : {{Monoid a}} -> Monad (Pair a)
  Monad-Pair ._>>=_ (u , x) k = let (v , y) = k x in (u <> v , y)

  Monad-Maybe : Monad Maybe
  Monad-Maybe ._>>=_ = \ where
    nothing _ -> nothing
    (just x) k -> k x

  Monad-List : Monad List
  Monad-List ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x <> (xs >>= k)

  Monad-IO : Monad IO
  Monad-IO ._>>=_ = bindIO

-------------------------------------------------------------------------------
-- Show
-------------------------------------------------------------------------------

ShowS : Set
ShowS = String -> String

record Show (a : Set) : Set where
  field showsPrec : Nat -> a -> ShowS

  shows : a -> ShowS
  shows = showsPrec 0

  show : a -> String
  show x = shows x ""

open Show {{...}} public

showString : String -> ShowS
showString = _<>_

showParen : Bool -> ShowS -> ShowS
showParen b p = if b then showString "(" <<< p <<< showString ")" else p

appPrec appPrec+1 : Nat
appPrec = 10
appPrec+1 = 11

instance
  Show-Void : Show Void
  Show-Void .showsPrec _ ()

  Show-Unit : Show Unit
  Show-Unit .showsPrec _ tt = showString "tt"

  Show-Bool : Show Bool
  Show-Bool .showsPrec _ b = showString (if b then "true" else "false")

  Show-Ordering : Show Ordering
  Show-Ordering .showsPrec _ = \ where
    LT -> showString "LT"
    EQ -> showString "EQ"
    GT -> showString "GT"

  Show-Nat : Show Nat
  Show-Nat .showsPrec _ = showString <<< String.primShowNat

  Show-Int : Show Int
  Show-Int .showsPrec _ = showString <<< Int.primShowInteger

  Show-Float : Show Float
  Show-Float .showsPrec _ = showString <<< Float.primShowFloat

  Show-Char : Show Char
  Show-Char .showsPrec _ = showString <<< String.primShowChar

  Show-String : Show String
  Show-String .showsPrec _ = showString <<< String.primShowString

  Show-Function : Show (Function a b)
  Show-Function .showsPrec _ _ = showString "<function>"

  Show-Pair : {{Show a}} -> {{Show b}} -> Show (Pair a b)
  Show-Pair .showsPrec prec (x , y) = showString "(" <<< showsPrec prec x
    <<< showString " , " <<< showsPrec prec y <<< showString ")"

  Show-Either : {{Show a}} -> {{Show b}} -> Show (Either a b)
  Show-Either .showsPrec prec = \ where
    (left x) -> showParen (prec > appPrec)
      (showString "left " <<< showsPrec appPrec+1 x)
    (right x) -> showParen (prec > appPrec)
      (showString "right " <<< showsPrec appPrec+1 x)

  Show-Maybe : {{Show a}} -> Show (Maybe a)
  Show-Maybe .showsPrec prec = \ where
    (just x) -> showParen (prec > appPrec)
      (showString "just " <<< showsPrec appPrec+1 x)
    nothing -> showString "nothing"

  Show-List : {{Show a}} -> Show (List a)
  Show-List .showsPrec prec = \ where
    [] -> showString "[]"
    (x :: xs) -> showParen (prec > appPrec)
      (showsPrec appPrec+1 x <<< showString " :: " <<< showsPrec 0 xs)
