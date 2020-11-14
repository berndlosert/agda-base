{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Trans.Class

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    t : (Set -> Set) -> Set -> Set

-------------------------------------------------------------------------------
-- MonadFree
-------------------------------------------------------------------------------

record MonadFree (f m : Set -> Set) : Set where
  field
    overlap {{Monad-m}} : Monad m
    wrap : f (m a) -> m a

  liftF : {{_ : Functor f}} -> f a -> m a
  liftF = wrap <<< map return

  wrapT : {{_ : Functor f}} {{_ : MonadTrans t}} -> f (t m a) -> t m a
  wrapT = join <<< lift <<< liftF

open MonadFree {{...}} public
