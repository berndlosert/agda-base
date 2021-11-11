module Control.Monad.Free.VL where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    m : Set -> Set
    f f1 f2 f3 f4 f5 f6 f7 f8 f9 : (Set -> Set) -> Set
    fs : List ((Set -> Set) -> Set)

-------------------------------------------------------------------------------
-- Effect / Effects
-------------------------------------------------------------------------------

Effect : Set
Effect = (Set -> Set) -> Set

infixr 4 _:<_
data Effects (m : Set -> Set) : List Effect -> Set where
  done : Effects m []
  _:<_ : f m -> Effects m fs -> Effects m (f :: fs)

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (f : Effect) (fs : List Effect) : Set where
  field getElem : Effects m fs -> f m

open Elem {{...}} public

instance
  Elem0 : Elem f (f :: fs)
  Elem0 .getElem (f :< _) = f

  Elem1 : Elem f (f1 :: f :: fs)
  Elem1 .getElem (_ :< f :< _) = f

  Elem2 : Elem f (f1 :: f2 :: f :: fs)
  Elem2 .getElem (_ :< _ :< f :< _) = f

  Elem3 : Elem f (f1 :: f2 :: f3 :: f :: fs)
  Elem3 .getElem (_ :< _ :< _ :< f :< _) = f

  Elem4 : Elem f (f1 :: f2 :: f3 :: f4 :: f :: fs)
  Elem4 .getElem (_ :< _ :< _ :< _ :< f :< _) = f

  Elem5 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f :: fs)
  Elem5 .getElem (_ :< _ :< _ :< _ :< _ :< f :< _) = f

  Elem6 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f :: fs)
  Elem6 .getElem (_ :< _ :< _ :< _ :< _ :< _ :< f :< _) = f

  Elem7 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f :: fs)
  Elem7 .getElem (_ :< _ :< _ :< _ :< _ :< _ :< _ :< f :< _) = f

  Elem8 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f :: fs)
  Elem8 .getElem (_ :< _ :< _ :< _ :< _ :< _ :< _ :< _ :< f :< _) = f

  Elem9 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f :: fs)
  Elem9 .getElem (_ :< _ :< _ :< _ :< _ :< _ :< _ :< _ :< _ :< f :< _) = f

-------------------------------------------------------------------------------
-- Free (van Laarhoven)
-------------------------------------------------------------------------------

record Free (fs : List Effect) (a : Set) : Set where
  constructor aFree
  field runFree : {{Monad m}} -> Effects m fs -> m a

open Free public

instance
  Functor-Free : Functor (Free fs)
  Functor-Free .map f program = aFree (map f <<< runFree program)

  Applicative-Free : Applicative (Free fs)
  Applicative-Free .pure x = aFree (const $ pure x)
  Applicative-Free ._<*>_ fs xs =
    aFree \ effects -> runFree fs effects <*> runFree xs effects

  Monad-Free : Monad (Free fs)
  Monad-Free ._>>=_ program k =
    aFree \ effects -> runFree program effects >>= \ x -> runFree (k x) effects

-- Because Elem-Implies and Elem-Obvious overlap, interpreting will not
-- work without Agda complaining.
interpret : {{Monad m}} -> Effects m fs -> Free fs a -> m a
interpret interpreter program = runFree program interpreter

liftFree : {{Elem f fs}} -> (forall {m} -> f m -> m a) -> Free fs a
liftFree getOp = aFree \ effects -> getOp (getElem effects)
