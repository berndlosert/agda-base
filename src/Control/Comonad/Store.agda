module Control.Comonad.Store where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private 
  variable 
    a s : Type

-------------------------------------------------------------------------------
-- Store
-------------------------------------------------------------------------------

data Store (s a : Type) : Type where
  store : (s -> a) -> s -> Store s a

runStore : Store s a -> Tuple (s -> a) s
runStore (store f x) = (f , x)

instance
  Functor-Store : Functor (Store s)
  Functor-Store .map f (store g s) = store (f <<< g) s

  Comonad-Store : Comonad (Store s)
  Comonad-Store .extend f x@(store g s) = store (\ _ -> f x) s
  Comonad-Store .extract (store g s) = g s
