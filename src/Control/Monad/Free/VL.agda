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
    f : (Set -> Set) -> Set

-------------------------------------------------------------------------------
-- Free (van Laarhoven)
-------------------------------------------------------------------------------

record Free (f : (Set -> Set) -> Set) (a : Set) : Set where
  field runFree : {{Monad m}} -> f m -> m a

open Free public

instance
  Functor-Free : Functor (Free f)
  Functor-Free .map f program .runFree = map f <<< runFree program

  Applicative-Free : Applicative (Free f)
  Applicative-Free .pure x .runFree = const (pure x)
  Applicative-Free ._<*>_ fs xs .runFree handler =
    runFree fs handler <*> runFree xs handler

  Monad-Free : Monad (Free f)
  Monad-Free ._>>=_ program k .runFree handler = do
    res <- runFree program handler
    runFree (k res) handler

interpret : {{Monad m}} -> f m -> Free f a -> m a
interpret handler program = runFree program handler

liftFree : (forall {m} -> f m -> m a) -> Free f a
liftFree getOp .runFree = getOp
