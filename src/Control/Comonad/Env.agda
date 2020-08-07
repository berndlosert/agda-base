module Control.Comonad.Env where

open import Control.Comonad
open import Prelude

private variable e : Set

-- The enivornment comonad. This is the dual of the Reader monad.
Env : Set -> Set -> Set
Env e a = e * a

instance
  FunctorEnv : Functor (Env e)
  FunctorEnv .map f (e , x) = (e , f x)

  ComonadEnv : Comonad (Env e)
  ComonadEnv .extend f p@(e , x) = (e , f p)
  ComonadEnv .extract (e , x) = x
