{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.VL where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

variable
  a : Set
  m : Set -> Set
  f g : (Set -> Set) -> Set
  fs : List ((Set -> Set) -> Set)

-------------------------------------------------------------------------------
-- Effect / Effects
-------------------------------------------------------------------------------

Effect : Set
Effect = (Set -> Set) -> Set

infixr 4 _:<_
data Effects (m : Set -> Set) : List Effect -> Set where
  Done : Effects m []
  _:<_ : f m -> Effects m fs -> Effects m (f :: fs)

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (f : Effect) (fs : List Effect) : Set where
  field getElem : Effects m fs -> f m

open Elem {{...}} public

instance
  Elem-Implies : {{Elem f fs}} -> Elem f (g :: fs)
  Elem-Implies .getElem (_ :< effs) = getElem effs

  Elem-Obvious : Elem f (f :: fs)
  Elem-Obvious .getElem (f :< _) = f

-------------------------------------------------------------------------------
-- Free (van Laarhoven)
-------------------------------------------------------------------------------

record Free (fs : List Effect) (a : Set) : Set where
  constructor Free:
  field runFree : {{Monad m}} -> Effects m fs -> m a

open Free public

instance
  Functor-Free : Functor (Free fs)
  Functor-Free .map f program = Free: (map f <<< runFree program)

  Applicative-Free : Applicative (Free fs)
  Applicative-Free .pure x = Free: (const $ pure x)
  Applicative-Free ._<*>_ fs xs =
    Free: \ effects -> runFree fs effects <*> runFree xs effects

  Monad-Free : Monad (Free fs)
  Monad-Free ._>>=_ program k =
    Free: \ effects -> runFree program effects >>= \ x -> runFree (k x) effects

-- Because Elem-Implies and Elem-Obvious overlap, interpreting will not
-- work without Agda complaining.
interpret : {{Monad m}} -> Effects m fs -> Free fs a -> m a
interpret interpreter program = runFree program interpreter

liftFree : {{Elem f fs}} -> (forall {m} -> f m -> m a) -> Free fs a
liftFree getOp = Free: \ effects -> getOp (getElem effects)
