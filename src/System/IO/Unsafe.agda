module System.IO.Unsafe where

open import Prelude

open import System.IO

private variable a : Set

postulate
  unsafePerformIO : IO a -> a

{-# FOREIGN GHC import qualified System.IO.Unsafe as U #-}
{-# COMPILE GHC unsafePerformIO = \ _ io -> U.unsafePerformIO io #-}
