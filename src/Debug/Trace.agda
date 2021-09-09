{-# OPTIONS --type-in-type #-}

module Debug.Trace where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import System.IO.Unsafe
open import String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- traceIO, trace, etc.
-------------------------------------------------------------------------------

postulate
  traceIO : String -> IO Unit

trace : String -> a -> a
trace string expr = unsafePerformIO do
  traceIO string
  pure expr

traceA : {{Applicative f}} -> String -> f Unit
traceA string = trace string $ pure tt

traceShow : {{Show a}} -> a -> b -> b
traceShow = trace <<< show

traceShowA : {{Show a}} -> {{Applicative f}} -> a -> f Unit
traceShowA = traceA <<< show

traceId : String -> String
traceId a = trace a a

traceShowId : {{Show a}} -> a -> a
traceShowId a = trace (show a) a

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Debug.Trace #-}
{-# FOREIGN GHC import Data.Text (unpack) #-}
{-# COMPILE GHC traceIO = traceIO . unpack #-}
