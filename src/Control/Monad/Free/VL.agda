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
-- Effect / Handler
-------------------------------------------------------------------------------

Effect : Set
Effect = (Set -> Set) -> Set

infixr 4 _:'_
data Handler : List Effect -> (Set -> Set) -> Set where
  [] : Handler [] m
  _:'_ : f m -> Handler fs m -> Handler (f :: fs) m

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (f : Effect) (fs : List Effect) : Set where
  field getElem : Handler fs m -> f m

open Elem {{...}} public

instance
  Elem0 : Elem f (f :: fs)
  Elem0 .getElem (f :' _) = f

  Elem1 : Elem f (f1 :: f :: fs)
  Elem1 .getElem (_ :' f :' _) = f

  Elem2 : Elem f (f1 :: f2 :: f :: fs)
  Elem2 .getElem (_ :' _ :' f :' _) = f

  Elem3 : Elem f (f1 :: f2 :: f3 :: f :: fs)
  Elem3 .getElem (_ :' _ :' _ :' f :' _) = f

  Elem4 : Elem f (f1 :: f2 :: f3 :: f4 :: f :: fs)
  Elem4 .getElem (_ :' _ :' _ :' _ :' f :' _) = f

  Elem5 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f :: fs)
  Elem5 .getElem (_ :' _ :' _ :' _ :' _ :' f :' _) = f

  Elem6 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f :: fs)
  Elem6 .getElem (_ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Elem7 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f :: fs)
  Elem7 .getElem (_ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Elem8 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f :: fs)
  Elem8 .getElem (_ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Elem9 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f :: fs)
  Elem9 .getElem (_ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

-------------------------------------------------------------------------------
-- Free (van Laarhoven)
-------------------------------------------------------------------------------

record Free (fs : List Effect) (a : Set) : Set where
  field runFree : {{Monad m}} -> Handler fs m -> m a

open Free public

instance
  Functor-Free : Functor (Free fs)
  Functor-Free .map f program .runFree = map f <<< runFree program

  Applicative-Free : Applicative (Free fs)
  Applicative-Free .pure x .runFree = const (pure x)
  Applicative-Free ._<*>_ fs xs .runFree handler =
    runFree fs handler <*> runFree xs handler

  Monad-Free : Monad (Free fs)
  Monad-Free ._>>=_ program k .runFree handler =
    runFree program handler >>= \ x -> runFree (k x) handler

interpret : {{Monad m}} -> Handler fs m -> Free fs a -> m a
interpret handler program = runFree program handler

liftFree : {{Elem f fs}} -> (forall {m} -> f m -> m a) -> Free fs a
liftFree getOp .runFree handler = getOp (getElem handler)
