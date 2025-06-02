module Control.Comonad.Env where

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
    e : Type

-------------------------------------------------------------------------------
-- Env
-------------------------------------------------------------------------------

data Env (e a : Type) : Type where
  env : e -> a -> Env e a

instance
  Functor-Env : Functor (Env e)
  Functor-Env .map f (env e x) = env e  (f x)

  Comonad-Env : Comonad (Env e)
  Comonad-Env .extend f p@(env e _)= env e (f p)
  Comonad-Env .extract (env e x) = x
