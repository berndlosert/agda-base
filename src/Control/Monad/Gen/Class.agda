module Control.Monad.Gen.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Bits
open import Data.List as List using ()
open import Data.List.Nonempty
open import Data.Monoid.Foldable
open import Data.Semigroup.Foldable
open import Data.Word

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Literals
-------------------------------------------------------------------------------

instance
  _ = FromNat-Nat1
  _ = FromNat-Int
  _ = FromNat-Float

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

private
  w64sToNat : List Word64 -> Nat
  w64sToNat [] = 0
  w64sToNat ws = go (List.reverse ws) 0
    where
      go : List Word64 -> Nat -> Nat
      go [] n = 0
      go (w :: ws) n = (toNat w) * 2 ^ (64 * n) + go ws (n + 1)

  log2 : Nat1 -> Nat
  log2 (suc n) =
    case (div (suc n) 2) \ where
      0 -> 0
      (suc m) -> 1 + log2 (suc m)

  -- ulpOfOne is the smallest value v satisfying
  --  * 1.0 + v /= 1.0
  --  * 1.0 + v / 2 == 1.0
  ulpOfOne/2 = 1.1102230246251565e-16

-------------------------------------------------------------------------------
-- MonadGen
-------------------------------------------------------------------------------

record MonadGen (m : Type -> Type) : Type where
  field
    overlap {{Monad-super}} : Monad m
    genWord64 : m Word64

  genBool : m Bool
  genBool = (| testBit genWord64 (pure 0) |)

  -- genBits n generates an n-bit number returned as a Nat.
  genBits : Nat1 -> m Nat
  genBits n = (| w64sToNat ws' |)
    where
      q = div (toNat n) 64
      r = mod (toNat n) 64
      mask = shiftR oneBits (64 - r)
      ws = List.replicateA (q + 1) genWord64
      ws' = List.modifyAt 0 (flip andBits mask) <$> ws

  -- genBoundedNat n generates a Nat in the range [0, n].
  genBoundedNat : Nat -> m Nat
  genBoundedNat 0 = pure 0
  genBoundedNat n+1@(suc n) =
      case (log2 (suc n)) \ where
        0 -> do
          b <- genBool
          pure $ if b then 0 else 1
        (suc N) -> go (suc N)
    where
      go : Nat1 -> m Nat
      go N = do
        m <- genBits N
        if m <= n+1 then pure m else go N

  -- getNatBetween m n generates a Nat in the range [m, n] if m <= n or [n, m] otherwise.
  genNatBetween : Nat -> Nat -> m Nat
  genNatBetween m n =
    let
      lo = min m n
      hi = max m n
    in
      if lo == hi
        then pure lo
        else do
          hi-lo <- genBoundedNat (hi - lo)
          pure (hi-lo + lo)

  -- getNat1Between m n generates a Nat1 in the range [m, n] if m <= n or [n, m] otherwise.
  genNat1Between : Nat1 -> Nat1 -> m Nat1
  genNat1Between (suc m) (suc n) = do
    k <- genNatBetween (suc m) (suc n)
    pure (suc (k - 1))

  -- genIntBetween i j generates an Int in the range [i, j] if i <= j or [j, i] otherwise.
  genIntBetween : Int -> Int -> m Int
  genIntBetween i j =
    let
      lo = min i j
      hi = max i j
    in
      if lo == hi
        then pure lo
        else do
          hi-lo <- genBoundedNat $ toNat (hi - lo)
          pure (fromNat hi-lo + lo)

  -- genSmallFloat generates a Float value in the range [0, 1).
  genSmallFloat : m Float
  genSmallFloat = do
    w <- genWord64
    let x = fromNat (toNat (shiftR w 11))
    pure (x * ulpOfOne/2)

  -- genFloatBetween x y generates a Float value in the range [x, y] if x <= y and [y, x] otherwise.
  genFloatBetween : Float -> Float -> m Float
  genFloatBetween x y =
    let
      lo = min x y
      hi = max x y
    in
      if lo == hi
        then pure lo
        else do
          z <- genSmallFloat
          pure (z * lo + (1.0 - z) * hi)

  genListOfSize : Nat -> m a -> m (List a)
  genListOfSize = List.replicateA

  genMaybe : m a -> m (Maybe a)
  genMaybe gen = do
    b <- genBool
    if b then just <$> gen else pure nothing

  genEither : m a -> m b -> m (Either a b)
  genEither x y = do
    b <- genBool
    if b then left <$> x else right <$> y

  genChooseFrom : List1 (m a) -> m a
  genChooseFrom (gen :: gens) = do
    n <- genBoundedNat (List.length gens)
    fromMaybe (List.at n gens) gen

  genElement : List1 a -> m a
  genElement xs = genChooseFrom (map pure xs)

  genUsingFrequency : List1 (Tuple Nat1 (m a)) -> m a
  genUsingFrequency freqs = do
      n <- genNat1Between 1 sumFreqs
      pickFrom freqs n
    where
      sumFreqs : Nat1
      sumFreqs = sum1 (fst <$> freqs)

      pickFrom : List1 (Tuple Nat1 (m a)) -> Nat1 -> m a
      pickFrom ((_ , g) :: rest) n =
        maybe g snd $ find (fst >>> (n <=_)) rest

  genSubsequence : List a -> m (List a)
  genSubsequence = List.filterA (const genBool)

  shuffle : List a -> m (List a)
  shuffle xs = do
      ns <- genListOfSize (List.length xs) (genNatBetween 0 2^32)
      pure (map snd (List.sortBy (compare on fst) (List.zip ns xs)))
    where
      2^32 : Nat
      2^32 = 4294967296

open MonadGen {{...}} public