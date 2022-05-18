module Debug where

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
    a b : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- trace, spy, etc.
-------------------------------------------------------------------------------

private
  postulate
    traceIO : String -> IO Unit

trace : String -> a -> a
trace s x = unsafePerformIO do
  traceIO s
  pure x

traceA : {{Applicative f}} -> String -> f Unit
traceA s = trace s $ pure tt

spy : {{Show a}} -> String -> a -> a
spy s x = trace (s <> ": " <> show x) x

spyWith : {{Show b}} -> String -> (a -> b) -> a -> a
spyWith s f x = trace (s <> ": " <> show (f x)) x

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Debug.Trace #-}
{-# FOREIGN GHC import Data.Text (unpack) #-}
{-# COMPILE GHC traceIO = traceIO . unpack #-}
