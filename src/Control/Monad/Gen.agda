module Control.Monad.Gen where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Gen.Class
open import Control.Monad.Gen.Trans
open import System.Random

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Gen.Class public
open Control.Monad.Gen.Trans public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a s : Type

-------------------------------------------------------------------------------
-- Gen
-------------------------------------------------------------------------------

Gen : Type -> Type
Gen a = GenT Identity a

runGen : {{RandomGen s}} -> Gen a -> s -> Tuple s a
runGen gen s = runIdentity (runGenT gen s)

evalGen : {{RandomGen s}} -> Gen a -> s -> a
evalGen gen s = snd (runGen gen s)