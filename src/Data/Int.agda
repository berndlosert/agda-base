{-# OPTIONS --type-in-type #-}

module Data.Int where

--open import Agda.Builtin.FromNeg public using (Negative)
open import Agda.Builtin.Int public using (Int; pos; negsuc)
open import Agda.Builtin.Nat public using (Nat; suc)
open import Data.Bool using (true; false)
open import Data.Division public using (Division; Nonzero; _/_; _%_)
open import Data.Eq using (Eq)
open import Data.Eq public using (Eq; _==_; _/=_)
open import Data.Nat using (Nat)
open import Data.Ord using (Ord)
open import Data.Ord public using (compare; LT; EQ; GT)
open import Data.Ord public using (_<_; _<=_; _>_; _>=_)
open import Data.Ord public using (min; max; comparing)
open import Data.Ring using (Ring)
open import Data.Ring public using (-_; _-_)
open import Data.Semiring using (Semiring; zero; one)
open import Data.Semiring public using (_+_; _*_)
open import Data.Unit using (Unit)
open import Data.Void using (Void)

private variable A : Set

foldZ : (Nat -> A) -> (Nat -> A) -> Int -> A
foldZ f g (pos n) = f n
foldZ f g (negsuc n) = g n

instance
  eqInt : Eq Int
  eqInt ._==_ = \ where
    (pos m) (pos n) -> m == n
    (negsuc m) (negsuc n) -> m == n
    _ _ -> false

  ordInt : Ord Int
  ordInt ._<_ = \ where
    (pos m) (pos n) -> m < n
    (negsuc m) (negsuc n) -> m > n
    (negsuc _) (pos _) -> true
    (pos _) (negsuc _) -> false

  semiringInt : Semiring Int
  ringInt : Ring Int
  semiringInt .zero = pos 0
  semiringInt .one = pos 1
  semiringInt ._+_ = \ where
      (negsuc m) (negsuc n) -> negsuc (suc (m + n))
      (negsuc m) (pos n) -> sub n (suc m)
      (pos m) (negsuc n) -> sub m (suc n)
      (pos m) (pos n) -> pos (m + n)
    where
      -- Subtracting two naturals to an integer result.
      sub : Nat -> Nat -> Int
      sub m 0 = pos m
      sub 0 (suc n) = negsuc n
      sub (suc m) (suc n) = sub m n
  semiringInt ._*_ = \ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> - (pos (n * suc m))
    (negsuc n) (pos m) -> - (pos (suc n * m))
  ringInt .-_ = \ where
    (pos 0) -> pos zero
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)
  ringInt ._-_ n m = n + (- m)

  --negativeInt : Negative Int
  --negativeInt = record {
  --    Constraint = \ _ -> Unit;
  --    fromNeg = \ where
  --      0 -> pos 0
  --      (suc n) -> negsuc n
  --  }

  divisionInt : Division Int
  divisionInt .Nonzero = \ where
    (pos 0) -> Void
    _ -> Unit
  divisionInt ._/_ = \ where
    (pos n) (pos m@(suc m-1)) -> pos (n / m)
    (negsuc n) (negsuc m) -> pos (suc n / suc m)
    (pos n) (negsuc m) -> - (pos (n / suc m))
    (negsuc n) (pos m@(suc m-1)) -> - (pos (suc n / m))
  divisionInt ._%_ = \ where
    (pos n) (pos m@(suc m-1)) -> pos (n % m)
    (negsuc n) (negsuc m) -> pos (suc n % suc m)
    (pos n) (negsuc m) -> - (pos (n % suc m))
    (negsuc n) (pos m@(suc m-1)) -> - (pos (suc n % m))
