{-# OPTIONS --type-in-type #-}

module Control.Monad.Error.Class where

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- MonadThrow
-------------------------------------------------------------------------------

record MonadThrow (e : Set) (m : Set -> Set) : Set where
  field throwError : e -> m a

open MonadThrow {{...}} public

-------------------------------------------------------------------------------
-- MonadError
-------------------------------------------------------------------------------

record MonadError (e : Set) (m : Set -> Set) : Set where
  field
    {{MonadThrow-super}} : MonadThrow e m
    catchError : m a -> (e -> m a) -> m a

open MonadError {{...}} public
