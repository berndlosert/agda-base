{-# OPTIONS --type-in-type #-}

module Control.Monad.Freer where

-- Freer is the composition of two free constructions: Coyoneda Sets and Free.
-- Thus, Freer F is a free monad for any function F : Set -> Set.

open import Control.Category
open import Control.Monad.Free
open import Data.Functor.Coyoneda

Freer : (Set -> Set) -> Set -> Set
Freer F = Free (Coyoneda Sets F)

-- Freer F is a functor in the same way that Free F is.

open import Data.Functor

instance
  Functor:Freer : forall {F} -> Endofunctor Sets (Freer F)
  Functor:Freer {F} .map f free alpha = map f (free alpha)

-- Freer F is a monad since Coyoneda Sets F is a functor.

open import Control.Monad

instance
  Monad:Freer : forall {F} -> Monad Sets (Freer F)
  Monad:Freer {F} = Monad:Free {Coyoneda Sets F}
    where instance _ = Functor:Coyoneda Sets F

-- The Freer analog of liftFree.

liftFreer : forall {F X} -> F X -> Freer F X
liftFreer = liftCoyoneda {Sets} >>> liftFree

-- The Freer analog of interpretFree.

interpretFreer : forall {F M}
  -> {{_ : Endofunctor Sets F}}
  -> {{_ : Monad Sets M}}
  -> (F ~> M) -> Freer F ~> M
interpretFreer = foldCoyoneda >>> interpretFree

-- The Freer analog of uninterpretFree.

uninterpretFreer : forall {F M} -> (Freer F ~> M) -> F ~> M
uninterpretFreer alpha x = alpha (liftFreer x)
