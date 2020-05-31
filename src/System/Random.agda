{-# OPTIONS --type-in-type #-}

module System.Random where

open import Prelude

open import Data.Bits using (_:|:_; shiftL; shiftR)
open import Data.Ref using (Ref; new; read; write; atomicModify)
open import Data.Word using (Word64; natToWord64; word64ToNat)
open import System.Time using (getTime; getCPUTime)

private variable A G : Set

--------------------------------------------------------------------------------
-- RandomGen
--------------------------------------------------------------------------------

record RandomGen (G : Set) : Set where
  field
    genNext : G -> Nat * G
    genRange : G -> Nat * Nat

open RandomGen {{...}} public

--------------------------------------------------------------------------------
-- LCG
--------------------------------------------------------------------------------

record LCG : Set where
  field
    modulus : Nat
    {{isNonzeroModulus}} : IsNonzero modulus
    multiplier : Nat
    {{isNonzeroMultiplier}} : IsNonzero multiplier
    increment : Nat
    seed : Nat

  generate : Nat
  generate = (multiplier * seed + increment) % modulus

instance
  genLCG : RandomGen LCG
  genLCG .genRange g = (0 , LCG.modulus g - 1)
  genLCG .genNext g = (n , g')
    where
      n = LCG.generate g
      g' = record g { seed = n }

--------------------------------------------------------------------------------
-- StdGen
--------------------------------------------------------------------------------

mkStdGen : Nat -> LCG
mkStdGen n = record {
    modulus = 2 ** 48;
    multiplier = 25214903917;
    increment = 11;
    seed = n
  }

private
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

  theStdGen : IO (Ref LCG)
  theStdGen = do
    ctr <- getTime
    key <- getCPUTime
    let seed = squares (natToWord64 ctr) (natToWord64 key)
    new (mkStdGen $ word64ToNat seed)

getStdGen : IO LCG
getStdGen = theStdGen >>= read

setStdGen : LCG -> IO Unit
setStdGen g = theStdGen >>= flip write g

getStdRandom : (LCG -> A * LCG) -> IO A
getStdRandom f = theStdGen >>= flip atomicModify (swap <<< f)

--------------------------------------------------------------------------------
-- Random
--------------------------------------------------------------------------------

record Random (A : Set) : Set where
  field
    random : {{_ : RandomGen G}} -> G -> A * G

  randomIO : IO A
  randomIO = getStdRandom random

open Random {{...}} public

instance
  randomUnit : Random Unit
  randomUnit .random g = (unit , g)

  randomBool : Random Bool
  randomBool .random g = let (n , g') = genNext g in
    ((n % 2) == 0 , g')

  randomNat : Random Nat
  randomNat .random g = genNext g
