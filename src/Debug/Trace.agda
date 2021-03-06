{-# OPTIONS --type-in-type #-}

module Debug.Trace where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import System.IO.Unsafe

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- traceIO, trace, etc.
-------------------------------------------------------------------------------

postulate
  traceIO : String -> IO Unit

trace : String -> a -> a
trace string expr = unsafePerformIO do
  traceIO string
  return expr

traceA : {{_ : Applicative f}} -> String -> f Unit
traceA string = trace string $ pure unit

traceShow : {{_ : Show a}} -> a -> b -> b
traceShow = trace <<< show

traceShowA : {{_ : Show a}} {{_ : Applicative f}} -> a -> f Unit
traceShowA = traceA <<< show

traceId : String -> String
traceId a = trace a a

traceShowId : {{_ : Show a}} -> a -> a
traceShowId a = trace (show a) a

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Debug.Trace #-}
{-# FOREIGN GHC import Data.Text (unpack) #-}
{-# COMPILE GHC traceIO = traceIO . unpack #-}
