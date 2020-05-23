{-# OPTIONS --type-in-type #-}

module System.Random where

open import Prelude

open import Data.Ref using (Ref; new; read; write)
open import System.IO.Unsafe using (unsafePerformIO)
open import System.Time using (getTime)

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
    modulus : Nonzero Nat
    multiplier : Nonzero Nat
    increment : Nat
    seed : Nat

  generate : Nat
  generate = (a * x + c) % m
    where
      a = getNonzero multiplier
      c = increment
      m = modulus
      x = seed

instance
  genLCG : RandomGen LCG
  genLCG .genRange g = (0 , getNonzero (LCG.modulus g) - 1)
  genLCG .genNext g = (n , g')
    where
      n = LCG.generate g
      g' = record g { seed = n }

--------------------------------------------------------------------------------
-- StdGen
--------------------------------------------------------------------------------

mkStdGen : Nat -> LCG
mkStdGen n = record {
    modulus = nonzero (2 ** 48);
    multiplier = nonzero 25214903917;
    increment = 11;
    seed = n
  }

private
  theStdGen : IO (Ref LCG)
  theStdGen = do
    t <- getTime
    new (mkStdGen t)

getStdGen : IO LCG
getStdGen = do
  g <- theStdGen
  read g

setStdGen : LCG -> IO Unit
setStdGen g = do
  g' <- theStdGen
  write g' g

--------------------------------------------------------------------------------
-- Random
--------------------------------------------------------------------------------

record Random (A : Set) : Set where
  field random : {{_ : RandomGen G}} -> G -> A * G

open Random {{...}} public

instance
  randomUnit : Random Unit
  randomUnit .random g = (unit , g)

  randomBool : Random Bool
  randomBool .random g = let (n , g') = genNext g in
    ((n % nonzero 2) == 0 , g')

  randomNat : Random Nat
  randomNat .random g = genNext g
