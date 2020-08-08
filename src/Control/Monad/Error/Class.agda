module Control.Monad.Error.Class where

private variable a : Set

record MonadError (e : Set) (m : Set -> Set) : Set where
  field
    throwError : e -> m a
    catchError : m a -> (e -> m a) -> m a

open MonadError {{...}} public
