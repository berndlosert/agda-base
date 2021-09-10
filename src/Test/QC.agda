{-# OPTIONS --type-in-type --guardedness #-}

module Test.QC where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Enum
open import Data.Float as Float using ()
open import Data.List as List using ()
open import Data.List1 as List1 using ()
open import Data.Stream as Stream using (Stream)
open import Data.String as String using ()
open import Data.Foldable
open import Data.Traversable
open import String.Show
open import System.IO
open import System.IO.Unsafe
open import System.Random

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open System.Random public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b g : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- Gen
-------------------------------------------------------------------------------

record Gen (a : Set) : Set where
  constructor toGen
  field unGen : StdGen -> Nat -> a

open Gen public

instance
  Functor-Gen : Functor Gen
  Functor-Gen .map f (toGen x) = toGen \ r n -> f (x r n)

  Applicative-Gen : Applicative Gen
  Applicative-Gen .pure x = toGen \ _ _ -> x
  Applicative-Gen ._<*>_ (toGen f) (toGen x) = toGen \ r n ->
    let (r1 , r2) = splitGen r in f r1 n (x r2 n)

  Monad-Gen : Monad Gen
  Monad-Gen ._>>=_ (toGen m) k = toGen \ r n ->
    let (r1 , r2) = splitGen r; toGen m' = k (m r1 n) in m' r2 n

-------------------------------------------------------------------------------
-- Gen combinators
-------------------------------------------------------------------------------

variant : Nat -> Gen a -> Gen a
variant v (toGen m) =
    toGen \ r n -> m (Stream.at (suc v) (rands r)) n
  where
    rands : {{RandomGen g}} -> g -> Stream g
    rands g = Stream.unfold splitGen g

generate' : Nat -> StdGen -> Gen a -> a
generate' n rnd (toGen m) = let (size , rnd') = randomR (0 , n) rnd in
  m rnd' size

sized : (Nat -> Gen a) -> Gen a
sized f = toGen \ r n -> let toGen m = f n in m r n

getSize : Gen Nat
getSize = sized pure

resize : Nat -> Gen a -> Gen a
resize n (toGen g) = toGen \ r _ -> g r n

scale : (Nat -> Nat) -> Gen a -> Gen a
scale f g = sized (\ n -> resize (f n) g)

choose : {{RandomR a}} -> Pair a a -> Gen a
choose rng = toGen \ r _ -> let (x , _) = randomR rng r in x

chooseAny : {{Random a}} -> Gen a
chooseAny = toGen \ r _ -> let (x , _) = random r in x

generate : Gen a -> IO a
generate (toGen g) = do
  r <- newStdGen
  pure (g r 30)

sample' : Gen a -> IO (List a)
sample' g = traverse generate do
  n <- 0 :: enumFromTo 2 20
  pure (resize n g)

sample : {{Show a}} -> Gen a -> IO Unit
sample g = do
  cases <- sample' g
  traverse! print cases

oneof : List1 (Gen a) -> Gen a
oneof (g :| gs) = do
  n <- choose (0 , length gs)
  fromMaybe g (List.at n gs)

frequency : List1 (Pair Nat1 (Gen a)) -> Gen a
frequency xs = do
    let sumFreqs = foldl _+_ (fst $ List1.head xs) (map fst $ List1.tail xs)
    n <- choose (1 , sumFreqs)
    fromMaybe (snd $ List1.head xs) (pick (toNat n) (toList xs))
  where
    pick : Nat -> List (Pair Nat1 (Gen a)) -> Maybe (Gen a)
    pick n [] = nothing
    pick n ((m , g) :: rest) =
      if n <= toNat m then just g else pick (n - toNat m) rest

elements : List1 a -> Gen a
elements (x :| xs) =
  let
    N = choose (0 , length xs)
    at n = fromMaybe x $ List.at n (x :: xs)
  in
    map at N

vectorOf : Nat -> Gen a -> Gen (List a)
vectorOf = List.replicateA

listOf : Gen a -> Gen (List a)
listOf gen = sized \ n -> do
  k <- choose (0 , n)
  vectorOf k gen

sublistOf : List a -> Gen (List a)
sublistOf = List.filterA \ _ -> choose (false , true)

shuffle : List a -> Gen (List a)
shuffle xs = do
    ns <- vectorOf (List.length xs) (choose (0 , 2^32))
    pure (map snd (List.sortBy (comparing fst) (List.zip ns xs)))
  where
    2^32 : Nat
    2^32 = 4294967296

delay : Gen (Gen a -> a)
delay = toGen \ r n g -> unGen g r n

promote : {{Monad m}} -> m (Gen a) -> Gen (m a)
promote m = do
  eval <- delay
  pure (map eval m)

-------------------------------------------------------------------------------
-- Arbitrary & Coarbitrary
-------------------------------------------------------------------------------

record Arbitrary (a : Set) : Set where
  field arbitrary : Gen a

open Arbitrary {{...}} public

arbitrary' : (a : Set) -> {{Arbitrary a}} -> Gen a
arbitrary' _ = arbitrary

record Coarbitrary (a : Set) : Set where
  field coarbitrary : a -> Gen b -> Gen b

open Coarbitrary {{...}} public

instance
  Arbitrary-Bool : Arbitrary Bool
  Arbitrary-Bool .arbitrary = elements (true :| false :: [])

  Arbitrary-Nat : Arbitrary Nat
  Arbitrary-Nat .arbitrary = sized \ n -> choose (0 , n)

  Arbitrary-Int : Arbitrary Int
  Arbitrary-Int .arbitrary = sized \ where
    0 -> choose (0 , 0)
    (suc n) -> choose (negsuc n , pos (suc n))

  Arbitrary-Float : Arbitrary Float
  Arbitrary-Float .arbitrary = sized \ n ->
    let n' = fromNat n
    in choose (- n' , n')

  Arbitrary-Pair : {{Arbitrary a}} -> {{Arbitrary b}} -> Arbitrary (Pair a b)
  Arbitrary-Pair .arbitrary = (| _,_ arbitrary arbitrary |)

  Arbitrary-List : {{Arbitrary a}} -> Arbitrary (List a)
  Arbitrary-List .arbitrary = sized \ n -> do
    m <- choose (0 , n)
    vectorOf m arbitrary

  Coarbitrary-Bool : Coarbitrary Bool
  Coarbitrary-Bool .coarbitrary b = variant (if b then 0 else 1)

  Coarbitrary-Pair : {{Coarbitrary a}} -> {{Coarbitrary b}}
    -> Coarbitrary (Pair a b)
  Coarbitrary-Pair .coarbitrary (a , b) = coarbitrary a <<< coarbitrary b

  Coarbitrary-List : {{Coarbitrary a}} -> Coarbitrary (List a)
  Coarbitrary-List .coarbitrary [] = variant 0
  Coarbitrary-List .coarbitrary (a :: as) =
    variant 1 <<< coarbitrary a <<< coarbitrary as

  Coarbitrary-Function : {{Arbitrary a}} -> {{Coarbitrary b}}
    -> Coarbitrary (a -> b)
  Coarbitrary-Function .coarbitrary f gen =
    arbitrary >>= (flip coarbitrary gen <<< f)

  Arbitrary-Function : {{Coarbitrary a}} -> {{Arbitrary b}}
    -> Arbitrary (a -> b)
  Arbitrary-Function .arbitrary = promote (flip coarbitrary arbitrary)

-------------------------------------------------------------------------------
-- Result & Property
-------------------------------------------------------------------------------

record Result : Set where
  field
    ok : Maybe Bool
    stamp : List String
    arguments : List String
    reason : String

record Property : Set where
  constructor toProperty
  field unProperty : Gen (IO Result)

open Property public

succeeded : Result
succeeded = record {
    ok = just true;
    stamp = [];
    arguments = [];
    reason = ""
  }

failed : Result
failed = record {
    ok = just false;
    stamp = [];
    arguments = [];
    reason = ""
  }

rejected : Result
rejected = record {
    ok = nothing;
    stamp = [];
    arguments = [];
    reason = ""
  }

result : Result -> Property
result = toProperty <<< pure <<< pure

-------------------------------------------------------------------------------
-- Testable
-------------------------------------------------------------------------------

record Testable (a : Set) : Set where
  field property : a -> Property

open Testable {{...}} public

forAll : {{Show a}} -> {{Testable b}} -> Gen a -> (a -> b) -> Property
forAll gen body = toProperty do
  a <- gen
  res <- unProperty $ property (body a)
  pure $ map (\ res -> record res { arguments = show a :: Result.arguments res }) res

infixr 0 _==>_
_==>_ : {{Testable a}} -> Bool -> a -> Property
true ==> a = property a
false ==> a = result rejected

label : {{Testable a}} -> String -> a -> Property
label s a = toProperty $ map (map add) (unProperty $ property a)
  where
    add : Result -> Result
    add res = record res { stamp = s :: Result.stamp res }

classify : {{Testable a}} -> Bool -> String -> a -> Property
classify true name = label name
classify false _ = property

collect : {{Show a}} -> {{Testable b}} -> a -> b -> Property
collect v = label (show v)

ioProperty : IO Property -> Property
ioProperty = map unProperty >>> promote >>> map join >>> toProperty

instance
  Testable-Unit : Testable Unit
  Testable-Unit .property _ = result succeeded

  Testable-Bool : Testable Bool
  Testable-Bool .property b = result (if b then succeeded else failed)

  Testable-Result : Testable Result
  Testable-Result .property = result

  Testable-Property : Testable Property
  Testable-Property .property = id

  Testable-Gen : {{Testable a}} -> Testable (Gen a)
  Testable-Gen .property gen = toProperty (gen >>= property >>> unProperty)

  Testable-Function : {{Arbitrary a}} -> {{Show a}} -> {{Testable b}}
    -> Testable (a -> b)
  Testable-Function .property f = forAll arbitrary f

-------------------------------------------------------------------------------
-- Config
-------------------------------------------------------------------------------

record Config : Set where
  field
    maxTest : Nat
    maxFail : Nat
    size : Nat -> Nat
    every : Nat -> List String -> String

quick : Config
quick = unsafePerform $
  record {
    maxTest = 100;
    maxFail = 1000;
    size = \ n -> n / 2 + 3;
    every = \ n args ->
      let s = show n in
      s <> String.replicate (String.length s) "\b"
  }

verbose : Config
verbose = record quick {
    every = \ n args -> show n <> ":\n" <> String.unlines args
  }

-------------------------------------------------------------------------------
-- check, quickCheck & verboseCheck
-------------------------------------------------------------------------------

private
  finish : String -> Nat -> List (List String) -> IO Unit
  finish mesg ntest stamps =
      do putStr (mesg <> " " <> show ntest <> " tests" <> table)
    where
      display : List String -> String
      display [] = ".\n"
      display (x :: []) = " (" <> x <> ").\n"
      display xs = ".\n" <> String.unlines (map (_<> ".") xs)

      pairLength : List (List String) -> Pair Nat (List String)
      pairLength [] = (0 , [])
      pairLength xss@(xs :: _) = (List.length xss , xs)

      percentage : Nat -> Nat -> Maybe String
      percentage n 0 = nothing
      percentage n (suc m) = just $ show ((100 * n) / suc m) <> "%"

      entry : Pair Nat (List String) -> String
      entry (n , s) = case percentage n ntest of \ where
        nothing -> ""
        (just p) -> p <> " " <> fold (List.intersperse ", " s)

      table : String
      table =
        ( display
        <<< map entry
        <<< List.reverse
        <<< List.sort
        <<< map pairLength
        <<< List.group
        <<< List.sort
        <<< List.filter (not <<< null)
        ) stamps

  {-# TERMINATING #-}
  tests : Config -> Property -> StdGen -> Nat -> Nat
    -> List (List String) -> IO Unit
  tests config prop@(toProperty gen) rnd0 ntest nfail stamps =
    if ntest == Config.maxTest config
      then finish "OK, passed" ntest stamps
      else if nfail == Config.maxFail config
        then finish "Arguments exhausted after" ntest stamps
        else do
          let (rnd1 , rnd2) = splitGen rnd0
          res <- generate' (Config.size config ntest) rnd2 gen
          putStr $ Config.every config ntest (Result.arguments res)
          case Result.ok res of \ where
            nothing -> tests
              config prop rnd1 ntest (nfail + 1) stamps
            (just true) -> tests
              config prop rnd1 (ntest + 1) nfail (Result.stamp res :: stamps)
            (just false) -> putStr $ "Falsifiable, after "
              <> show ntest
              <> " tests:\n"
              <> String.unlines (Result.arguments res)

check : {{Testable a}} -> Config -> a -> IO Unit
check cfg a = do
  rnd <- newStdGen
  tests cfg (property a) rnd 0 0 []

quickCheck : {{Testable a}} -> a -> IO Unit
quickCheck = check quick

verboseCheck : {{Testable a}} -> a -> IO Unit
verboseCheck = check verbose
