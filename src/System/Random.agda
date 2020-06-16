{-# OPTIONS --type-in-type #-}

module System.Random where

open import Prelude

open import Data.Bits
open import Data.Ref
open import Data.Word
open import System.IO.Unsafe
open import System.Time

private variable A As G : Set

--------------------------------------------------------------------------------
-- RandomGen
--------------------------------------------------------------------------------

record RandomGen (G : Set) : Set where
  field
    genWord64 : G -> Word64 * G
    splitGen : G -> G * G

open RandomGen {{...}} public

-- genBits n generates a random n-bit number.
genBits : {{_ : RandomGen G}} -> Nat -> G -> Nat * G
genBits {G} n g0 =
    fst $ foldr accum (first word64ToNat (genWord64' g0) , 1) q
  where
    q = n / 64
    r = n % 64
    mask = shiftR oneBits (64 - r)

    -- This will generate a Word64 value in the range [0, 2 ^ r).
    genWord64' : G -> Word64 * G
    genWord64' g = first (_:&: mask) (genWord64 g)

    -- We use this to build up the random number in the foldr expression.
    accum : Unit -> (Nat * G) * Nat -> (Nat * G) * Nat
    accum _ ((m , g) , i) =
      let
        (w , g') = genWord64 g
        m' = m + 2 ^ (64 * i) * word64ToNat w
      in
        (m' , g' , i + 1)

-- genNat n generates a Nat in the range [0 , n].
{-# TERMINATING #-}
genNat : {{_ : RandomGen G}} -> Nat -> G -> Nat * G
genNat {G} n g0 = loop g0
  where
    log2 : Nat -> Nat
    log2 0 = 1
    log2 m = 1 + log2 (m / 2)

    k = log2 n

    loop : G -> Nat * G
    loop g = let (m , g') = genBits k g in
      if m > n then loop g' else (m , g')

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
  randomGenStdGen .genWord64 (stdGen: seed gamma) =
      (mix64 seed' , stdGen: seed' gamma)
    where
      seed' = seed + gamma
  randomGenStdGen .splitGen (stdGen: seed gamma) =
      (stdGen: seed'' gamma , stdGen: (mix64 seed') (mixGamma seed''))
    where
      seed' = seed + gamma
      seed'' = seed' + gamma

mkStdGen : Word64 -> StdGen
mkStdGen s = stdGen: (mix64 s) (mixGamma (s + goldenGamma))

theStdGen : Ref StdGen
theStdGen = unsafePerformIO $ do
  ctr <- getTime
  key <- getCPUTime
  let seed = squares (natToWord64 ctr) (natToWord64 key)
  new (mkStdGen seed)
{-# NOINLINE theStdGen #-}

newStdGen : IO StdGen
newStdGen = atomicModify theStdGen splitGen

getStdGen : IO StdGen
getStdGen = read theStdGen

setStdGen : StdGen -> IO Unit
setStdGen = write theStdGen

getStdRandom : (StdGen -> A * StdGen) -> IO A
getStdRandom f = atomicModify theStdGen (swap <<< f)

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
  randomBool : Random Bool
  randomBool .random g = let (n , g') = genWord64 g in
    (testBit n 0 , g')

  {-# TERMINATING #-}
  randomRNat : RandomR Nat
  randomRNat .randomR (from , to) g with compare from to
  ... | EQ = (from , g)
  ... | GT = randomR (to , from) g
  ... | LT = first (_+ from) $ genNat (to - from) g
