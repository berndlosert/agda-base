{-# OPTIONS --type-in-type #-}

module System.Random where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Bits
open import Data.Float as Float using ()
open import Data.Int as Int using ()
open import Data.IORef
open import Data.List as List using ()
open import Data.Word
open import System.Time

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a as g : Type

-------------------------------------------------------------------------------
-- RandomGen
-------------------------------------------------------------------------------

record RandomGen (g : Type) : Type where
  field
    genWord64 : g -> Pair Word64 g
    splitGen : g -> Pair g g

open RandomGen {{...}} public

private
  -- Convert a list of Word64 values, considered as one long word, into a Nat.
  w64sToNat : List Word64 -> Nat
  w64sToNat [] = 0
  w64sToNat ws = go (List.reverse ws) 0
    where
      go : List Word64 -> Nat -> Nat
      go [] n = 0
      go (w :: ws) n = (toNat w) * 2 ^ (64 * n) + go ws (n + 1)

-- Generates n random Word64 values.
genWord64s : {{RandomGen g}} -> Nat -> g -> Pair (List Word64) g
genWord64s 0 g0 = ([] , g0)
genWord64s (Suc n) g0 =
  let
    (w , g1) = genWord64 g0
    (ws , g) = genWord64s n g1
  in
    (w :: ws , g)

-- genNat n generates a random Nat in the range [0, 2 ^ n).
genNat : {{RandomGen g}} -> Nat -> g -> Pair Nat g
genNat n g0 =
  let
    q = div n 64
    r = mod n 64
    mask = shiftR oneBits (64 - r)
    (ws , g) = genWord64s (q + 1) g0
  in
    case ws of \ where
      (h :: t) -> (w64sToNat ((h :&: mask) :: t) , g)
      [] -> (0 , g)

-- genNat' n generates a Nat in the range [0 , n].
{-# TERMINATING #-}
genNat' : {{RandomGen g}} -> Nat -> g -> Pair Nat g
genNat' {g} n g0 = loop g0
  where
    log2 : Nat -> Nat
    log2 0 = 1
    log2 m = 1 + log2 (div m 2)

    k = log2 n

    loop : g -> Pair Nat g
    loop g = let (m , g') = genNat k g in
      if m > n then loop g' else (m , g')

-- genFloat generates a Float value in the range [0, 1).
genFloat : {{RandomGen g}} -> g -> Pair Float g
genFloat g = let (w , g') = genWord64 g in
    (fromNat (toNat (shiftR w 11)) * ulpOfOne/2 , g')
  where
    -- ulpOfOne is the smallest value v satisfying
    --  * 1.0 + v /= 1.0
    --  * 1.0 + v / 2 == 1.0
    ulpOfOne/2 = 1.1102230246251565e-16

-------------------------------------------------------------------------------
-- StdGen (SplitMix version)
-------------------------------------------------------------------------------

record StdGen : Type where
  constructor stdgen:
  field
    seed : Word64
    gamma : Word64 -- must be odd

private
  goldengamma : Word64
  goldengamma = 0x9e3779b97f4a7c15

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

  mixgamma : Word64 -> Word64
  mixgamma z0 =
    let
      z1 = mix64variant13 z0 :|: 1
      n = popCount (z1 xor (shiftR z1 1))
    in
      if n >= 24 then z1 else z1 xor 0xaaaaaaaaaaaaaaaa

  -- Squares: a Fast Counter-Based RNG
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
  RandomGen-StdGen : RandomGen StdGen
  RandomGen-StdGen .genWord64 (stdgen: seed gamma) =
      (mix64 seed' , stdgen: seed' gamma)
    where
      seed' = seed + gamma
  RandomGen-StdGen .splitGen (stdgen: seed gamma) =
      (stdgen: seed'' gamma , stdgen: (mix64 seed') (mixgamma seed''))
    where
      seed' = seed + gamma
      seed'' = seed' + gamma

mkStdGen : Word64 -> StdGen
mkStdGen s = stdgen: (mix64 s) (mixgamma (s + goldengamma))

theStdGen : IO (IORef StdGen)
theStdGen = do
  ctr <- getPOSIXTime
  key <- getCPUTime
  let seed = squares (fromNat ctr) (fromNat key)
  newIORef (mkStdGen seed)

newStdGen : IO StdGen
newStdGen = do
  ref <- theStdGen
  atomicModifyIORef ref splitGen

getStdGen : IO StdGen
getStdGen = do
  ref <- theStdGen
  readIORef ref

setStdGen : StdGen -> IO Unit
setStdGen gen = do
  ref <- theStdGen
  writeIORef ref gen

getStdRandom : (StdGen -> Pair a StdGen) -> IO a
getStdRandom f = do
  ref <- theStdGen
  atomicModifyIORef ref (swap <<< f)

-------------------------------------------------------------------------------
-- Random
-------------------------------------------------------------------------------

record Random (a : Type) : Type where
  field random : {{RandomGen g}} -> g -> Pair a g

  randomIO : IO a
  randomIO = getStdRandom random

open Random {{...}} public

instance
  Random-Bool : Random Bool
  Random-Bool .random g = let (n , g') = genWord64 g in
    (testBit n 0 , g')

-------------------------------------------------------------------------------
-- RandomR
-------------------------------------------------------------------------------

record RandomR (a : Type) : Type where
  field randomR : {{RandomGen g}} -> Pair a a -> g -> Pair a g

  randomRIO : Pair a a -> IO a
  randomRIO = getStdRandom <<< randomR

open RandomR {{...}} public

instance
  RandomR-Bool : RandomR Bool
  RandomR-Bool .randomR (False , False) g = (False , g)
  RandomR-Bool .randomR (True , True) g = (True , g)
  RandomR-Bool .randomR _ g = flip lmap (genNat' 1 g) \ where
    0 -> False
    _ -> True

  RandomR-Nat : RandomR Nat
  RandomR-Nat .randomR (m , n) g =
    let
      lo = min m n
      hi = max m n
    in
      if lo == hi
        then (lo , g)
        else lmap (_+ lo) (genNat' (hi - lo) g)

  RandomR-Int : RandomR Int
  RandomR-Int .randomR (i , j) g =
    let
      lo = min i j
      hi = max i j
    in
      if lo == hi
        then (lo , g)
        else lmap (\ n -> fromNat n + lo)
          (genNat' (toNat (hi - lo) {{trustMe}}) g)

  RandomR-Float : RandomR Float
  RandomR-Float .randomR (x , y) g =
    let
      lo = min x y
      hi = max x y
    in
      if lo == hi
        then (lo , g)
        else lmap (\ x -> x * lo + (1.0 - x) * hi) (genFloat g)
