module Test.QC.Poly where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Gen.Class
open import Data.List.Nonempty
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    m : Type -> Type

-------------------------------------------------------------------------------
-- A, B, C
-------------------------------------------------------------------------------

data A : Type where
  a1 a2 : A

data B : Type where
  b1 b2 b3 : B

data C : Type where
  c1 c2 c3 c4 : C

genA : {{MonadGen m}} -> m A
genA = genElement (a1 :: a2 :: [])

genB : {{MonadGen m}} -> m B
genB = genElement (b1 :: b2 :: b3 :: [])

genC : {{MonadGen m}} -> m C
genC = genElement (c1 :: c2 :: c3 :: c4 :: [])

instance
  Eq-A : Eq A
  Eq-A ._==_ = \ where
    a1 a1 -> true
    a2 a2 -> true
    _ _ -> false

  Eq-B : Eq B
  Eq-B ._==_ = \ where
    b1 b1 -> true
    b2 b2 -> true
    b3 b3 -> true
    _ _ -> false

  Eq-C : Eq C
  Eq-C ._==_ = \ where
    c1 c1 -> true
    c2 c2 -> true
    c3 c3 -> true
    c4 c4 -> true
    _ _ -> false

  Show-A : Show A
  Show-A .showsPrec prec = \ where
    a1 -> "a1"
    a2 -> "a2"
  Show-A .show = showDefault

  Show-B : Show B
  Show-B .showsPrec prec = \ where
    b1 -> "b1"
    b2 -> "b2"
    b3 -> "b3"
  Show-B .show = showDefault

  Show-C : Show C
  Show-C .showsPrec prec = \ where
    c1 -> "c1"
    c2 -> "c2"
    c3 -> "c3"
    c4 -> "c4"
  Show-C .show = showDefault
