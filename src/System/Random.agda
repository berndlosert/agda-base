{-# OPTIONS --type-in-type #-}

module System.Random where

open import Prelude

open import Data.Ref using (Ref; new; read; write; atomicModify)
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
  theStdGen : IO (Ref LCG)
  theStdGen = getTime >>= mkStdGen >>> new

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
