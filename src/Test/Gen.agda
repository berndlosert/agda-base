{-# OPTIONS --type-in-type #-}

module Test.Gen where

open import Prelude

open import Data.Bits
open import Data.List
open import System.Random public

private variable A : Set

record Gen (A : Set) : Set where
  constructor gen:
  field unGen : StdGen -> Nat -> A

instance
  functorGen : Functor Gen
  functorGen .map f (gen: h) = gen: \ r n -> f (h r n)

  applicativeGen : Applicative Gen
  applicativeGen .pure x = gen: \ _ _ -> x
  applicativeGen ._<*>_ (gen: f) (gen: x) = gen: \ r n -> f r n (x r n)

  monadGen : Monad Gen
  monadGen ._>>=_ (gen: m) k = gen: \ r n ->
    case splitGen r of \ where
      (r1 , r2) -> let gen: m' = k (m r1 n) in m' r2 n

{-
private
  integerVariant : forall {G} {{_ : RandomGen G}} -> Int -> G -> G
  integerVariant {G} n g =
      let (l , r) = splitGen g in
      if n >= 1
      then gamma n l
      else gamma (1 - n) r
    where
      ilog2 : Int -> Int
      ilog2 (pos 1) = 0
      ilog2 n = 1 + ilog2 (n / 2)

      gamma : Int -> G -> G
      gamma n = let k = ilog2 n in encode k <<< zeroes k
        where
          encode : Int -> G -> G
          encode (negsuc 0) g = g
          encode k g =
            let (l , r) = splitGen g in
            if testBit n k
            then encode (k - 1) r
            else encode (k - 1) l

          zeroes : Int -> G -> G
          zeroes 0 g = g
          zeroes k g =
            let (l , _) = splitGen g in
            zeroes (k - 1) l
-}
--variant : Nat -> Gen A -> Gen A
--variant k (gen: g) = gen: \ r n -> g (k $ r) n

sized : (Nat -> Gen A) -> Gen A
sized f = gen: \ r n -> let gen: m = f n in m r n

getSize : Gen Nat
getSize = sized pure

resize : Nat -> Gen A -> Gen A
resize n (gen: g) = gen: \ r _ -> g r n

scale : (Nat -> Nat) -> Gen A -> Gen A
scale f g = sized (\ n -> resize (f n) g)

choose : {{_ : RandomR A}} -> A * A -> Gen A
choose rng = gen: \ r _ -> let (x , _) = randomR rng r in x

chooseAny : {{_ : Random A}} -> Gen A
chooseAny = gen: \ r _ -> let (x , _) = random r in x

generate : Gen A -> IO A
generate (gen: g) = do
  r <- newStdGen
  return (g r 30)

sample' : Gen A -> IO (List A)
sample' g = traverse generate $ do
  n <- 0 :: (range 2 20)
  return (resize n g)

sample : {{_ : Show A}} -> Gen A -> IO Unit
sample g = do
  cases <- sample' g
  traverse! print cases

oneof : (gs : List (Gen A)) {_ : IsNonempty gs} -> Gen A
oneof gs = do
  n <- choose (0 , count gs - 1)
  fromJust (at n gs) {believeMe}
