{-# OPTIONS --type-in-type #-}

module System.Random where

open import Prelude

open import Data.Bits
open import Data.Ref
open import Data.Word
open import System.Time

private variable A As G : Set

--------------------------------------------------------------------------------
-- RandomGen
--------------------------------------------------------------------------------

record RandomGen (G : Set) : Set where
  field
    genRange : G -> Nat * Nat
    genNext : G -> Nat * G
    genSplit : G -> G * G

open RandomGen {{...}} public

--------------------------------------------------------------------------------
-- StdGen (SplitMix version)
--------------------------------------------------------------------------------

record StdGen : Set where
  constructor stdGen:
  field
    seed : Word64
    gamma : Word64 -- must be odd

private
  goldenGamma : Word64
  goldenGamma = 0x9e3779b97f4a7c15

  mix64 : Word64 -> Word64
  mix64 z0 = z3
    where
      z1 = (z0 xor (shiftR z0 33)) * 0xff51afd7ed558ccd
      z2 = (z1 xor (shiftR z1 33)) * 0xc4ceb9fe1a85ec53
      z3 = z2 xor (shiftR z2 33)

  mix64variant13 : Word64 -> Word64
  mix64variant13 z0 = z3
    where
      z1 = (z0 xor (shiftR z0 30)) * 0xbf58476d1ce4e5b9
      z2 = (z1 xor (shiftR z1 27)) * 0x94d049bb133111eb
      z3 = z2 xor (shiftR z2 31)

  mixGamma : Word64 -> Word64
  mixGamma z0 =
    let
      z1 = mix64variant13 z0 :|: 1
      n = popCount (z1 xor (shiftR z1 1))
    in
      if n >= 24 then z1 else z1 xor 0xaaaaaaaaaaaaaaaa

  -- Squares: A Fast Counter-Based RNG
  -- https://arxiv.org/pdf/2004.06278v2.pdf
  squares : Word64 -> Word64 -> Word64
  squares ctr key =
    let
      x0 = ctr * key
      y = x0
      z = y + key
      -- Round 1
      x1 = x0 * x0 + y
      x2 = (shiftR x1 32) :|: (shiftL x1 32)
      -- Round 2
      x3 = x2 * x2 + z
      x4 = (shiftR x3 32) :|: (shiftL x3 32)
    in
      shiftR (x4 * x4 + y) 32

instance
  randomGenStdGen : RandomGen StdGen
  randomGenStdGen .genRange _ = (0 , 2 ^ 64)
  randomGenStdGen .genNext (stdGen: seed gamma) =
      (word64ToNat (mix64 seed') , stdGen: seed' gamma)
    where
      seed' = seed + gamma
  randomGenStdGen .genSplit (stdGen: seed gamma) =
      (stdGen: seed'' gamma , stdGen: (mix64 seed') (mixGamma seed''))
    where
      seed' = seed + gamma
      seed'' = seed' + gamma

mkStdGen : Word64 -> StdGen
mkStdGen s = stdGen: (mix64 s) (mixGamma (s + goldenGamma))

theStdGen : IO (Ref StdGen)
theStdGen = do
  ctr <- getTime
  key <- getCPUTime
  let seed = squares (natToWord64 ctr) (natToWord64 key)
  new (mkStdGen seed)

newStdGen : IO StdGen
newStdGen = do
  ref <- theStdGen
  atomicModify ref genSplit

getStdGen : IO StdGen
getStdGen = theStdGen >>= read

setStdGen : StdGen -> IO Unit
setStdGen g = theStdGen >>= flip write g

getStdRandom : (StdGen -> A * StdGen) -> IO A
getStdRandom f = theStdGen >>= flip atomicModify (swap <<< f)

--------------------------------------------------------------------------------
-- Random and RandomR
--------------------------------------------------------------------------------

record Random (A : Set) : Set where
  field random : {{_ : RandomGen G}} -> G -> A * G

  randomIO : IO A
  randomIO = getStdRandom random

open Random {{...}} public

record RandomR (A : Set) : Set where
  field
    randomR : {{_ : RandomGen G}} -> A * A -> G -> A * G

  randomRIO : A * A -> IO A
  randomRIO = getStdRandom <<< randomR

open RandomR {{...}} public

instance
  randomUnit : Random Unit
  randomUnit .random g = (unit , g)

  randomBool : Random Bool
  randomBool .random g = let (n , g') = genNext g in
    ((n % 2) == 0 , g')

  {-# TERMINATING #-}
  randomRNat : RandomR Nat
  randomRNat .randomR (from , to) g with compare from to
  ... | EQ = (from , g)
  ... | GT = randomR (to , from) g
  ... | LT =
    let
      (lo , hi) = genRange g
      diff = hi - lo
      instance diffNonzero : IsNonzero diff
      diffNonzero = believeMe
      (r , g') = genNext g
    in
      (r * (to - from) / diff , g')
