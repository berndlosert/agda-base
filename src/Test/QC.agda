{-# OPTIONS --type-in-type #-}

module Test.QC where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.Constraint.Positive
open import Data.List as List using ()
open import Data.Stream as Stream using (Stream)
open import Data.String as String using ()
open import Data.Foldable
open import Data.Traversable
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
  constructor Gen:
  field unGen : StdGen -> Nat -> a

open Gen public

instance
  Functor-Gen : Functor Gen
  Functor-Gen .map f (Gen: x) = Gen: \ r n -> f (x r n)

  Applicative-Gen : Applicative Gen
  Applicative-Gen .pure x = Gen: \ _ _ -> x
  Applicative-Gen ._<*>_ (Gen: f) (Gen: x) = Gen: \ r n ->
    let (r1 , r2) = splitGen r in f r1 n (x r2 n)

  Monad-Gen : Monad Gen
  Monad-Gen ._>>=_ (Gen: m) k = Gen: \ r n ->
    let (r1 , r2) = splitGen r; Gen: m' = k (m r1 n) in m' r2 n

-------------------------------------------------------------------------------
-- Gen combinators
-------------------------------------------------------------------------------

variant : Nat -> Gen a -> Gen a
variant v (Gen: m) =
    Gen: \ r n -> m (Stream.at (Suc v) (rands r)) n
  where
    rands : {{_ : RandomGen g}} -> g -> Stream g
    rands g = Stream.unfold splitGen g

generate' : Nat -> StdGen -> Gen a -> a
generate' n rnd (Gen: m) = let (size , rnd') = randomR (0 , n) rnd in
  m rnd' size

sized : (Nat -> Gen a) -> Gen a
sized f = Gen: \ r n -> let Gen: m = f n in m r n

getSize : Gen Nat
getSize = sized pure

resize : Nat -> Gen a -> Gen a
resize n (Gen: g) = Gen: \ r _ -> g r n

scale : (Nat -> Nat) -> Gen a -> Gen a
scale f g = sized (\ n -> resize (f n) g)

choose : {{_ : RandomR a}} -> a * a -> Gen a
choose rng = Gen: \ r _ -> let (x , _) = randomR rng r in x

chooseAny : {{_ : Random a}} -> Gen a
chooseAny = Gen: \ r _ -> let (x , _) = random r in x

generate : Gen a -> IO a
generate (Gen: g) = do
  r <- newStdGen
  return (g r 30)

sample' : Gen a -> IO (List a)
sample' g = traverse generate do
  n <- 0 :: enumFromTo 2 20
  return (resize n g)

sample : {{_ : Show a}} -> Gen a -> IO Unit
sample g = do
  cases <- sample' g
  traverse! print cases

oneof : (gs : List (Gen a)) {{_ : IsNonempty gs}} -> Gen a
oneof gs = do
  n <- choose (0 , length gs - 1)
  fromJust (List.at n gs) {{trustMe}}

frequency : (xs : List (Positive Nat * Gen a)) {{_ : IsNonempty xs}} -> Gen a
frequency xs =
    let xs' = map (bimap unconstrained id) xs
    in choose (1 , sum (map fst xs')) >>= flip pick xs'
  where
    pick : Nat -> List (Nat * Gen a) -> Gen a
    pick n ((k , y) :: ys) = if n <= k then y else pick (n - k) ys
    pick n [] = undefined -- No worries. We'll never see this case.

elements : (xs : List a) {{_ : IsNonempty xs}} -> Gen a
elements xs = map
  (\ n -> fromJust (List.at n xs) {{trustMe}})
  (choose {Nat} (0 , List.length xs - 1))

vectorOf : Nat -> Gen a -> Gen (List a)
vectorOf = List.replicateA

listOf : Gen a -> Gen (List a)
listOf gen = sized \ n -> do
  k <- choose (0 , n)
  vectorOf k gen

sublistOf : List a -> Gen (List a)
sublistOf = List.filterA \ _ -> map (_== 0) (choose {Nat} (0 , 1))

shuffle : List a -> Gen (List a)
shuffle xs = do
  ns <- vectorOf (List.length xs) (choose {Nat} (0 , 2 ^ 32))
  return (map snd (List.sortBy (comparing fst) (List.zip ns xs)))

delay : Gen (Gen a -> a)
delay = Gen: \ r n g -> unGen g r n

promote : {{_ : Monad m}} -> m (Gen a) -> Gen (m a)
promote m = do
  eval <- delay
  return (map eval m)

-------------------------------------------------------------------------------
-- Arbitrary & Coarbitrary
-------------------------------------------------------------------------------

record Arbitrary (a : Set) : Set where
  field arbitrary : Gen a

open Arbitrary {{...}} public

record Coarbitrary (a : Set) : Set where
  field coarbitrary : a -> Gen b -> Gen b

open Coarbitrary {{...}} public

instance
  Arbitrary-Bool : Arbitrary Bool
  Arbitrary-Bool .arbitrary = elements (True :: False :: [])

  Arbitrary-Nat : Arbitrary Nat
  Arbitrary-Nat .arbitrary = sized \ n -> choose (0 , n)

  Arbitrary-Int : Arbitrary Int
  Arbitrary-Int .arbitrary = sized \ where
    0 -> choose (0 , 0)
    (Suc n) -> choose (NegSuc n , Pos (Suc n))

  Arbitrary-Float : Arbitrary Float
  Arbitrary-Float .arbitrary = sized \ n ->
    let n' = toFloat n
    in choose (- n' , n')

  Arbitrary-Tuple : {{_ : Arbitrary a}} {{_ : Arbitrary b}} -> Arbitrary (a * b)
  Arbitrary-Tuple .arbitrary = (| _,_ arbitrary arbitrary |)

  Arbitrary-List : {{_ : Arbitrary a}} -> Arbitrary (List a)
  Arbitrary-List .arbitrary = sized \ n -> do
    m <- choose (0 , n)
    vectorOf m arbitrary

  Coarbitrary-Bool : Coarbitrary Bool
  Coarbitrary-Bool .coarbitrary b = variant (if b then 0 else 1)

  Coarbitrary-Tuple : {{_ : Coarbitrary a}} {{_ : Coarbitrary b}}
    -> Coarbitrary (a * b)
  Coarbitrary-Tuple .coarbitrary (a , b) = coarbitrary a <<< coarbitrary b

  Coarbitrary-List : {{_ : Coarbitrary a}} -> Coarbitrary (List a)
  Coarbitrary-List .coarbitrary [] = variant 0
  Coarbitrary-List .coarbitrary (a :: as) =
    variant 1 <<< coarbitrary a <<< coarbitrary as

  Coarbitrary-Function : {{_ : Arbitrary a}} {{_ : Coarbitrary b}}
    -> Coarbitrary (a -> b)
  Coarbitrary-Function .coarbitrary f gen =
    arbitrary >>= (flip coarbitrary gen <<< f)

  Arbitrary-Function : {{_ : Coarbitrary a}} {{_ : Arbitrary b}}
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

Property : Set
Property = Gen (IO Result)

succeeded : Result
succeeded = record { ok = Just True; stamp = []; arguments = [] }

failed : Result
failed = record { ok = Just False; stamp = []; arguments = [] }

rejected : Result
rejected = record { ok = Nothing; stamp = []; arguments = [] }

result : Result -> Property
result res = return (return res)

-------------------------------------------------------------------------------
-- Testable
-------------------------------------------------------------------------------

record Testable (a : Set) : Set where
  field property : a -> Property

open Testable {{...}} public

forAll : {{_ : Show a}} {{_ : Testable b}} -> Gen a -> (a -> b) -> Property
forAll gen body = do
  a <- gen
  res <- property (body a)
  return $ map (\ res -> record res { arguments = show a :: Result.arguments res }) res

infixr 0 _==>_
_==>_ : {{_ : Testable a}} -> Bool -> a -> Property
True ==> a = property a
False ==> a = result rejected

label : {{_ : Testable a}} -> String -> a -> Property
label s a = map (map add) (property a)
  where
    add : Result -> Result
    add res = record res { stamp = s :: Result.stamp res }

classify : {{_ : Testable a}} -> Bool -> String -> a -> Property
classify True name = label name
classify False _ = property

collect : {{_ : Show a}} {{_ : Testable b}} -> a -> b -> Property
collect v = label (show v)

instance
  Testable-Unit : Testable Unit
  Testable-Unit .property _ = result succeeded

  Testable-Bool : Testable Bool
  Testable-Bool .property b = result (if b then succeeded else failed)

  Testable-Result : Testable Result
  Testable-Result .property = return <<< return

  Testable-Property : Testable Property
  Testable-Property .property = id

  Testable-Gen : {{_ : Testable a}} -> Testable (Gen a)
  Testable-Gen .property = _>>= property

  Testable-Function : {{_ : Arbitrary a}} {{_ : Show a}} {{_ : Testable b}}
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
quick = record {
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
  done : String -> Nat -> List (List String) -> IO Unit
  done mesg ntest stamps =
      do putStr (mesg <> " " <> show ntest <> " tests" <> table)
    where
      display : List String -> String
      display [] = ".\n"
      display [ x ] = " (" <> x <> ").\n"
      display xs = ".\n" <> String.unlines (map (_<> ".") xs)

      pairLength : List (List String) -> Nat * List String
      pairLength [] = (0 , [])
      pairLength xss@(xs :: _) = (List.length xss , xs)

      percentage : Nat -> Nat -> String
      percentage n 0 = undefined -- No worries; we'll never use this case
      percentage n m@(Suc _) = show ((100 * n) / m) <> "%"

      entry : Nat * (List String) -> String
      entry (n , s) = percentage n ntest
        <> " "
        <> fold (List.intersperse ", " s)

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
  tests config gen rnd0 ntest nfail stamps =
    if ntest == Config.maxTest config
    then (do done "OK, passed" ntest stamps)
    else if nfail == Config.maxFail config
    then (do done "Arguments exhausted after" ntest stamps)
    else (
      let
        (rnd1 , rnd2) = splitGen rnd0
      in do
        result <- generate' (Config.size config ntest) rnd2 gen
        putStr (Config.every config ntest (Result.arguments result))
        case Result.ok result of \ where
          Nothing -> tests
            config gen rnd1 ntest (nfail + 1) stamps
          (Just True) -> tests
            config gen rnd1 (ntest + 1) nfail (Result.stamp result :: stamps)
          (Just False) -> putStr ("Falsifiable, after "
            <> show ntest
            <> " tests:\n"
            <> String.unlines (Result.arguments result))
      )

check : {{_ : Testable a}} -> Config -> a -> IO Unit
check cfg a = do
  rnd <- newStdGen
  tests cfg (property a) rnd 0 0 []

quickCheck : {{_ : Testable a}} -> a -> IO Unit
quickCheck = check quick

verboseCheck : {{_ : Testable a}} -> a -> IO Unit
verboseCheck = check verbose
