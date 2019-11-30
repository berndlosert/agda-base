{-# OPTIONS --type-in-type #-}

module Control.Monad.Freer where

open import Control.Category
open import Control.Monad
open import Control.Monad.Free 
open import Data.Functor
open import Data.Functor.Coyoneda

-- Freer is the composition of two free constructions: Coyoneda Sets and Free.
-- Thus, Freer F is a free monad for any function F : Set -> Set.
Freer : (Set -> Set) -> Set -> Set
Freer F = Free (Coyoneda Sets F) 

-- Freer F is a functor in the same way that Free F is.
instance Functor:Freer : {F : Set -> Set} -> Endofunctor Sets (Freer F)
Functor:Freer {F} .map f free alpha = map f (free alpha) 

-- Freer F is a monad since Coyoneda Sets F is a functor.
instance Monad:Freer : {F : Set -> Set} -> Monad Sets (Freer F)
Monad:Freer {F} = Monad:Free {Coyoneda Sets F} 
  where instance _ = Functor:Coyoneda Sets F

-- The Freer analog of liftFree.
liftFreer : {F : Set -> Set} {X : Set} -> F X -> Freer F X
liftFreer = liftCoyoneda {Sets} >>> liftFree

-- The Freer analog of foldFree. 
foldFreer : {F M : Set -> Set} 
  -> {{_ : Endofunctor Sets F}} 
  -> {{_ : Monad Sets M}}
  -> (F ⇒ M) -> Freer F ⇒ M 
foldFreer = foldCoyoneda >>> foldFree

-- The Freer analog of ladjunctFree.
ladjunctFreer : {F M : Set -> Set} -> (Freer F ⇒ M) -> F ⇒ M
ladjunctFreer alpha x = alpha (liftFreer x)
