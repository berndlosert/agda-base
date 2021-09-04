{-# OPTIONS --type-in-type #-}

module Data.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import String.Show

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

data Fin (n : Nat) {{_ : Assert $ n /= 0}} : Set where
  Fin: : (m : Nat) -> Fin n

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

module _ {n : Nat} {{_ : Assert $ n /= 0}} where
  instance
    Eq-Fin : Eq (Fin n)
    Eq-Fin ._==_ (Fin: k) (Fin: m) = rem k n == rem m n

    Ord-Fin : Ord (Fin n)
    Ord-Fin .compare (Fin: k) (Fin: m) = compare (rem k n) (rem m n)

    FromNat-Fin : FromNat (Fin n)
    FromNat-Fin .FromNatConstraint _ = Unit
    FromNat-Fin .fromNat m = Fin: m

    ToNat-Fin : ToNat (Fin n)
    ToNat-Fin .ToNatConstraint _ = Unit
    ToNat-Fin .toNat (Fin: m) = rem m n

    Semigroup-Additive-Fin : Semigroup (Additive (Fin n))
    Semigroup-Additive-Fin ._<>_ x y =
        Additive: $ plus (getAdditive x) (getAdditive y)
      where
        plus : Fin n -> Fin n -> Fin n
        plus (Fin: k) (Fin: m) = Fin: $ rem (k + m) n

    Semigroup-Multiplicative-Fin : Semigroup (Multiplicative (Fin n))
    Semigroup-Multiplicative-Fin ._<>_ x y =
        Multiplicative: $ mul (getMultiplicative x) (getMultiplicative y)
      where
        mul : Fin n -> Fin n -> Fin n
        mul (Fin: k) (Fin: m) = Fin: $ rem (k * m) n

    Monoid-Additive-Fin : Monoid (Additive (Fin n))
    Monoid-Additive-Fin .neutral = Additive: 0

    Monoid-Multiplicative-Fin : Monoid (Multiplicative (Fin n))
    Monoid-Multiplicative-Fin .neutral = Multiplicative: 1

    Group-Additive-Fin : Group (Additive (Fin n))
    Group-Additive-Fin .invert x = neutral ~~ x
    Group-Additive-Fin ._~~_ x y =
        Additive: $ minus (getAdditive x) (getAdditive y)
      where
        minus : Fin n -> Fin n -> Fin n
        minus (Fin: k) (Fin: m) =
          Fin: $ if k >= m then rem (monus k m) n else monus n (rem (monus m k) n)

    Show-Fin : Show (Fin n)
    Show-Fin .showsPrec _ m = showString $ show $ toNat m
