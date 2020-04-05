{-# OPTIONS --type-in-type #-}

module Prelude where

private
  variable
    A B C D : Set
    F G M : Set -> Set

--------------------------------------------------------------------------------
-- For notational convenience
--------------------------------------------------------------------------------

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
  monoidString .mempty = ""

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
dupe = split id id

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
untag = either id id

isLeft : A + B -> Bool
isLeft = either (const true) (const false)

isRight : A + B -> Bool
isRight = not <<< isLeft

fromLeft : A -> A + B -> A
fromLeft x = either id (const x)

fromRight : B -> A + B -> B
fromRight y = either (const y) id

fromEither : (A -> B) -> A + B -> B
fromEither f = either f id

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

isJust : Maybe A -> Bool
isJust (just _) = true
isJust _ = false

isNothing : Maybe A -> Bool
isNothing = not <<< isJust

maybe : B -> (A -> B) -> Maybe A -> B
maybe b f nothing = b
maybe b f (just a) = f a

fromMaybe : A -> Maybe A -> A
fromMaybe = flip maybe id

maybeToLeft : B -> Maybe A -> A + B
maybeToLeft b = maybe (right b) left

maybeToRight : B -> Maybe A -> B + A
maybeToRight b = mirror <<< maybeToLeft b

leftToMaybe : A + B -> Maybe A
leftToMaybe = either just (const nothing)

rightToMaybe : A + B -> Maybe B
rightToMaybe = leftToMaybe <<< mirror

ensure : (A -> Bool) -> A -> Maybe A
ensure p a = if p a then just a else nothing

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

  alternativeMaybe : Alternative Maybe
  alternativeMaybe .empty = nothing
  alternativeMaybe ._<|>_ = \ where
    nothing r -> r
    l _ -> l

  monadMaybe : Monad Maybe
  monadMaybe ._>>=_ = \ where
    nothing k -> nothing
    (just x) k -> k x

  semigroupMaybe : {{_ : Semigroup A}} -> Semigroup (Maybe A)
  semigroupMaybe ._<>_ = \ where
    nothing m -> m
    m nothing -> m
    (just x) (just y) -> just (x <> y)

  monoidMaybe : {{_ : Semigroup A}} -> Monoid (Maybe A)
  monoidMaybe .mempty = nothing

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

  alternativeList : Alternative List
  alternativeList .empty = []
  alternativeList ._<|>_ = _++_

  monadList : Monad List
  monadList ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x ++ (xs >>= k)

  semigroupList : Semigroup (List A)
  semigroupList ._<>_ = _++_

  monoidList : Monoid (List A)
  monoidList .mempty = []

til : Nat -> List Nat
til 0 = []
til (suc n) = til n ++ pure n

range : Nat -> Nat -> List Nat
range m n with compare m n
... | GT = []
... | EQ = pure n
... | LT = map (_+ m) $ til $ suc (n - m)

--------------------------------------------------------------------------------
-- Function and Endo
--------------------------------------------------------------------------------

record Endo A : Set where
  constructor toEndo
  field fromEndo : A -> A

open Endo public

instance
  semigroupFunction : {{_ : Semigroup B}} -> Semigroup (A -> B)
  semigroupFunction ._<>_ f g = \ a -> f a <> g a

  monoidFunction : {{_ : Monoid B}} -> Monoid (A -> B)
  monoidFunction .mempty = const mempty

  semigroupEndo : Semigroup (Endo A)
  semigroupEndo ._<>_ g f = toEndo (fromEndo g <<< fromEndo f)

  monoidEndo : Monoid (Endo A)
  monoidEndo .mempty = toEndo id

--------------------------------------------------------------------------------
-- Id
--------------------------------------------------------------------------------

record Id (A : Set) : Set where
  constructor toId
  field fromId : A

open Id public

instance
  functorId : Functor Id
  functorId .map f = toId <<< f <<< fromId

  applicativeId : Applicative Id
  applicativeId .pure = toId
  applicativeId ._<*>_ = map <<< fromId

  monadId : Monad Id
  monadId ._>>=_ a k = k (fromId a)

  eqId : {{_ : Eq A}} -> Eq (Id A)
  eqId ._==_ x y = fromId (| _==_ x y |)

  ordId : {{_ : Ord A}} -> Ord (Id A)
  ordId ._<_ x y = fromId (| _<_ x y |)

  semigroupId : {{_ : Semigroup A}} -> Semigroup (Id A)
  semigroupId ._<>_ x y = (| _<>_ x y |)

  monoidId : {{_ : Monoid A}} -> Monoid (Id A)
  monoidId .mempty = toId mempty

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

  showNat : Show Nat
  showNat .show = Agda.Builtin.String.primShowNat

  showInt : Show Int
  showInt .show = Agda.Builtin.Int.primShowInteger

  showFloat : Show Float
  showFloat .show = Agda.Builtin.Float.primShowFloat

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

  showList : forall {A} {{_ : Show A}} -> Show (List A)
  showList .show [] = "[]"
  showList {A} .show as = "(" ++ show' as ++ ")"
    where
      show' : List A -> String
      show' [] = "[]"
      show' (x :: xs) = show x ++ " :: " ++ show' xs

  showChar : Show Char
  showChar .show c = "'" ++ pack (pure c) ++ "'"

  showString : Show String
  showString .show = Agda.Builtin.String.primShowString

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
  monoidIO .mempty = return mempty

print : {{_ : Show A}} -> A -> IO Unit
print x = putStrLn (show x)

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStr (f s)
