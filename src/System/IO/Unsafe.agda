{-# OPTIONS --type-in-type #-}

module System.IO.Unsafe where

open import Prelude

private variable a : Type

postulate
  unsafePerformIO : IO a -> a

{-# FOREIGN GHC import qualified System.IO.Unsafe as U #-}
{-# COMPILE GHC unsafePerformIO = \ _ io -> U.unsafePerformIO io #-}
