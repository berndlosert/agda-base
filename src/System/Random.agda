module System.Random where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Gen.Class
open import Data.Bits
open import Data.IORef
open import Data.Word
open import System.Time

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- RandomGen
-------------------------------------------------------------------------------

record RandomGen (g : Type) : Type where
  field
    nextWord64 : g -> Tuple g Word64
    split : g -> Tuple g g

open RandomGen {{...}} public

-------------------------------------------------------------------------------
-- StdGen (based on SplitMix)
-------------------------------------------------------------------------------

private
  StdGen' : Type
  StdGen' = Tuple Word64 Word64

  goldengamma : Word64
  goldengamma = 0x9e3779b97f4a7c15

  mix64 : Word64 -> Word64
  mix64 z0 = z3
    where
      z1 = (xorBits z0 (shiftR z0 33)) * 0xff51afd7ed558ccd
      z2 = (xorBits z1 (shiftR z1 33)) * 0xc4ceb9fe1a85ec53
      z3 = xorBits z2 (shiftR z2 33)

  mix64variant13 : Word64 -> Word64
  mix64variant13 z0 = z3
    where
      z1 = (xorBits z0 (shiftR z0 30)) * 0xbf58476d1ce4e5b9
      z2 = (xorBits z1 (shiftR z1 27)) * 0x94d049bb133111eb
      z3 = xorBits z2 (shiftR z2 31)

  mixgamma : Word64 -> Word64
  mixgamma z0 =
    let
      z1 = orBits (mix64variant13 z0) 1
      n = popCount (xorBits z1 (shiftR z1 1))
    in
      if n >= 24 then z1 else (xorBits z1 0xaaaaaaaaaaaaaaaa)

-- https://arxiv.org/pdf/2004.06278v2.pdf
  squares : Word64 -> Word64 -> Word64
  squares ctr key =
    let
      x0 = ctr * key
      y = x0
      z = y + key
      -- Round 1
      x1 = x0 * x0 + y
      x2 = orBits (shiftR x1 32) (shiftL x1 32)
      -- Round 2
      x3 = x2 * x2 + z
      x4 = orBits (shiftR x3 32) (shiftL x3 32)
      -- Round 3
      x5 = shiftR (x4 * x4 + y) 32
    in
      x5

StdGen = StdGen'

instance
  RandomGen-StdGen : RandomGen StdGen
  RandomGen-StdGen .nextWord64 (seed , gamma) =
      ((seed1 , gamma) , mix64 seed1)
    where
      seed1 = seed + gamma
  RandomGen-StdGen .split (seed , gamma) =
      ((seed2 , gamma) , (mix64 seed1 , mixgamma seed2))
    where
      seed1 = seed + gamma
      seed2 = seed1 + gamma

mkStdGen : Word64 -> StdGen
mkStdGen w = (mix64 w , mixgamma (w + goldengamma))

theStdGen : IO (IORef StdGen)
theStdGen = do
  ctr <- getPOSIXTime
  key <- getCPUTime
  let seed = squares (fromNat ctr) (fromNat key)
  newIORef (mkStdGen seed)

newStdGen : IO StdGen
newStdGen = do
  ref <- theStdGen
  atomicModifyIORef ref split

getStdGen : IO StdGen
getStdGen = readIORef =<< theStdGen

setStdGen : StdGen -> IO Unit
setStdGen gen = do
  ref <- theStdGen
  writeIORef ref gen

instance
  MonadGen-IO : MonadGen IO
  MonadGen-IO .genWord64 = do
    rng <- newStdGen
    pure (snd (nextWord64 rng))