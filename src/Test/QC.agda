{-# OPTIONS --type-in-type #-}

module Test.QC where

open import Prelude

open import Data.Bits
open import Data.Ix
open import Data.List
open import Data.Stream as Stream using (Stream)
open import Data.String as String using ()
open import System.Random public

private variable A B G : Set

--------------------------------------------------------------------------------
-- Gen
--------------------------------------------------------------------------------

record Gen (A : Set) : Set where
  constructor gen:
  field unGen : StdGen -> Nat -> A

instance
  functorGen : Functor Gen
  functorGen .map f (gen: h) = gen: λ r n -> f (h r n)

  applicativeGen : Applicative Gen
  applicativeGen .pure x = gen: λ _ _ -> x
  applicativeGen ._<*>_ (gen: f) (gen: x) = gen: λ r n -> f r n (x r n)

  monadGen : Monad Gen
  monadGen ._>>=_ (gen: m) k = gen: λ r n ->
    case split r of λ where
      (r1 , r2) -> let gen: m' = k (m r1 n) in m' r2 n

--------------------------------------------------------------------------------
-- Gen combinators
--------------------------------------------------------------------------------

variant : Nat -> Gen A -> Gen A
variant v (gen: m) =
    gen: λ r n -> m (Stream.at (suc v) (rands r)) n
  where
    rands : {{_ : RandomGen G}} -> G -> Stream G
    rands g = Stream.unfold split g

generate' : Nat -> StdGen -> Gen A -> A
generate' n rnd (gen: m) = let (size , rnd') = randomR (0 , n) rnd in
  m rnd' size

sized : (Nat -> Gen A) -> Gen A
sized f = gen: λ r n -> let gen: m = f n in m r n

getSize : Gen Nat
getSize = sized pure

resize : Nat -> Gen A -> Gen A
resize n (gen: g) = gen: λ r _ -> g r n

scale : (Nat -> Nat) -> Gen A -> Gen A
scale f g = sized (λ n -> resize (f n) g)

choose : {{_ : RandomR A}} -> A * A -> Gen A
choose rng = gen: λ r _ -> let (x , _) = randomR rng r in x

chooseAny : {{_ : Random A}} -> Gen A
chooseAny = gen: λ r _ -> let (x , _) = random r in x

generate : Gen A -> IO A
generate (gen: g) = do
  r <- newStdGen
  return (g r 30)

sample' : Gen A -> IO (List A)
sample' g = traverse generate $ do
  n <- 0 :: range (2 , 20)
  return (resize n g)

sample : {{_ : Show A}} -> Gen A -> IO Unit
sample g = do
  cases <- sample' g
  traverse! print cases

oneof : (gs : List (Gen A)) {{_ : Nonempty gs}} -> Gen A
oneof gs = do
  n <- choose (0 , count gs - 1)
  fromJust (at n gs) {{believeMe}}

frequency : (xs : List (Nat * Gen A)) {{_ : So $ sum (map fst xs) > 0}}
  -> Gen A
frequency {A} xs = choose (1 , tot) >>= (λ x -> pick x xs)
  where
    tot = sum (map fst xs)

    pick : Nat -> List (Nat * Gen A) -> Gen A
    pick n ((k , y) :: ys) = if n <= k then y else pick (n - k) ys
    pick n [] = undefined -- No worries. We'll never see this case.

elements : (xs : List A) {{_ : Nonempty xs}} -> Gen A
elements xs = map
  (λ n -> fromJust (at n xs) {{believeMe}})
  (choose {Nat} (0 , length xs - 1))

vectorOf : Nat -> Gen A -> Gen (List A)
vectorOf = replicateA

listOf : Gen A -> Gen (List A)
listOf gen = sized λ n -> do
  k <- choose (0 , n)
  vectorOf k gen

sublistOf : List A -> Gen (List A)
sublistOf xs = filterA (λ _ -> map (_== 0) $ choose {Nat} (0 , 1)) xs

shuffle : List A -> Gen (List A)
shuffle xs = do
  ns <- vectorOf (length xs) (choose {Nat} (0 , 2 ^ 32))
  return (map snd (sortBy (comparing fst) (zip ns xs)))

promote : (A -> Gen B) -> Gen (A -> B)
promote f = gen: λ r n a -> let (gen: m) = f a in m r n

--------------------------------------------------------------------------------
-- Arbitrary & Coarbitrary
--------------------------------------------------------------------------------

record Arbitrary (A : Set) : Set where
  field arbitrary : Gen A

open Arbitrary {{...}} public

record Coarbitrary (A : Set) : Set where
  field coarbitrary : A -> Gen B -> Gen B

open Coarbitrary {{...}} public

instance
  arbitraryBool : Arbitrary Bool
  arbitraryBool .arbitrary = elements (True :: False :: [])

  arbitraryNat : Arbitrary Nat
  arbitraryNat .arbitrary = sized λ n -> choose (0 , n)

  arbitraryInt : Arbitrary Int
  arbitraryInt .arbitrary = sized λ where
    0 -> choose (0 , 0)
    (suc n) -> choose (negsuc n , pos (suc n))

  arbitraryTuple : {{_ : Arbitrary A}} {{_ : Arbitrary B}} -> Arbitrary (A * B)
  arbitraryTuple .arbitrary = (| _,_ arbitrary arbitrary |)

  arbitraryList : {{_ : Arbitrary A}} -> Arbitrary (List A)
  arbitraryList .arbitrary = sized λ n -> do
    m <- choose (0 , n)
    vectorOf m arbitrary

  coarbitraryBool : Coarbitrary Bool
  coarbitraryBool .coarbitrary b = variant (if b then 0 else 1)

  coarbitraryTuple : {{_ : Coarbitrary A}} {{_ : Coarbitrary B}}
    -> Coarbitrary (A * B)
  coarbitraryTuple .coarbitrary (a , b) = coarbitrary a ∘ coarbitrary b

  coarbitraryList : {{_ : Coarbitrary A}} -> Coarbitrary (List A)
  coarbitraryList .coarbitrary [] = variant 0
  coarbitraryList .coarbitrary (a :: as) =
    variant 1 ∘ coarbitrary a ∘ coarbitrary as

  coarbitraryFunction : {{_ : Arbitrary A}} {{_ : Coarbitrary B}}
    -> Coarbitrary (A -> B)
  coarbitraryFunction .coarbitrary f gen =
    arbitrary >>= (flip coarbitrary gen ∘ f)

  arbitraryFunction : {{_ : Coarbitrary A}} {{_ : Arbitrary B}}
    -> Arbitrary (A -> B)
  arbitraryFunction .arbitrary = promote (flip coarbitrary arbitrary)

--------------------------------------------------------------------------------
-- Result & Property
--------------------------------------------------------------------------------

record Result : Set where
  field
    ok : Maybe Bool
    stamp : List String
    arguments : List String

record Property : Set where
  constructor property:
  field result : Gen Result

none : Result
none = record { ok = nothing; stamp = []; arguments = [] }

result : Result -> Property
result res = property: (return res)

--------------------------------------------------------------------------------
-- Testable
--------------------------------------------------------------------------------

record Testable (A : Set) : Set where
  field property : A -> Property

open Testable {{...}}

evaluate : {{_ : Testable A}} -> A -> Gen Result
evaluate a = let (property: gen) = property a in gen

forAll : {{_ : Show A}} {{_ : Testable B}} -> Gen A -> (A -> B) -> Property
forAll gen body = property: do
  a <- gen
  res <- evaluate (body a)
  return (record res { arguments = show a :: Result.arguments res })

infixr 0 _==>_
_==>_ : {{_ : Testable A}} -> Bool -> A -> Property
True ==> a = property a
False ==> a = result none

label : {{_ : Testable A}} -> String -> A -> Property
label s a = property: (add <$> evaluate a)
  where
    add : Result -> Result
    add res = record res { stamp = s :: Result.stamp res }

classify : {{_ : Testable A}} -> Bool -> String -> A -> Property
classify True name = label name
classify False _ = property

collect : {{_ : Show A}} {{_ : Testable B}} -> A -> B -> Property
collect v = label (show v)

instance
  testableBool : Testable Bool
  testableBool .property b = result (record none { ok = just b })

  testableProperty : Testable Property
  testableProperty .property prop = prop

  testableFunction : {{_ : Arbitrary A}} {{_ : Show A}} {{_ : Testable B}}
    -> Testable (A -> B)
  testableFunction .property f = forAll arbitrary f

--------------------------------------------------------------------------------
-- Config
--------------------------------------------------------------------------------

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
    size = λ n -> n / 2 + 3;
    every = λ n args ->
      let s = show n in
      s ++ pack (replicate (String.length s) '\b')
  }

verbose : Config
verbose = record quick {
    every = λ n args -> show n ++ ":\n" ++ String.unlines args
  }

--------------------------------------------------------------------------------
-- check, quickCheck & verboseCheck
--------------------------------------------------------------------------------

private
  done : String -> Nat -> List (List String) -> IO Unit
  done mesg ntest stamps =
      do putStr (mesg ++ " " ++ show ntest ++ " tests" ++ table)
    where
      display : List String -> String
      display [] = ".\n"
      display [ x ] = " (" ++ x ++ ").\n"
      display xs = ".\n" ++ String.unlines (map (_++ ".") xs)

      pairLength : List (List String) -> Nat * List String
      pairLength [] = (0 , [])
      pairLength xss@(xs :: _) = (length xss , xs)

      percentage : Nat -> Nat -> String
      percentage n 0 = undefined -- No worries; we'll never use this case
      percentage n m@(suc _) = show ((100 * n) / m) ++ "%"

      entry : Nat * (List String) -> String
      entry (n , s) = percentage n ntest
        ++ " "
        ++ String.concat (intersperse ", " s)

      table : String
      table = display
        ∘ map entry
        ∘ reverse
        ∘ sort
        ∘ map pairLength
        ∘ group
        ∘ sort
        ∘ filter (not ∘ null)
        $ stamps

  {-# TERMINATING #-}
  tests : Config -> Gen Result -> StdGen -> Nat -> Nat
    -> List (List String) -> IO Unit
  tests config gen rnd0 ntest nfail stamps =
    if ntest == Config.maxTest config
    then (do done "OK, passed" ntest stamps)
    else if nfail == Config.maxFail config
    then (do done "Arguments exhausted after" ntest stamps)
    else (
      let
        (rnd1 , rnd2) = split rnd0
        result = generate' (Config.size config ntest) rnd2 gen
      in do
        putStr (Config.every config ntest (Result.arguments result))
        case Result.ok result of λ where
          nothing -> tests
            config gen rnd1 ntest (nfail + 1) stamps
          (just True) -> tests
            config gen rnd1 (ntest + 1) nfail (Result.stamp result :: stamps)
          (just False) -> putStr ("Falsifiable, after "
            ++ show ntest
            ++ " tests:\n"
            ++ String.unlines (Result.arguments result))
      )

check : {{_ : Testable A}} -> Config -> A -> IO Unit
check config a = do
  rnd <- newStdGen
  tests config (evaluate a) rnd 0 0 []

quickCheck : {{_ : Testable A}} -> A -> IO Unit
quickCheck = check quick

verboseCheck : {{_ : Testable A}} -> A -> IO Unit
verboseCheck = check verbose
