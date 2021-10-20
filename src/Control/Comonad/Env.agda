module Control.Comonad.Env where

open import Control.Comonad
open import Prelude

private variable e : Set

-- The enivornment comonad. This is the dual of the Reader monad.
Env : Set -> Set -> Set
Env e a = Pair e a

instance
  Functor-Env : Functor (Env e)
  Functor-Env .map f (e , x) = (e , f x)

  Comonad-Env : Comonad (Env e)
  Comonad-Env .extend f p@(e , x) = (e , f p)
  Comonad-Env .extract (e , x) = x
