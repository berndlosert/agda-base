module Control.Monad.Reader where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Reader.Class
open import Control.Monad.Reader.Trans

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Reader.Class public
open Control.Monad.Reader.Trans public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b r r' : Type

-------------------------------------------------------------------------------
-- Reader
-------------------------------------------------------------------------------

Reader : Type -> Type -> Type
Reader r = ReaderT r Identity

{-# DISPLAY ReaderT r Identity = Reader r #-}

runReader : Reader r a -> r -> a
runReader m = runIdentity <<< runReaderT m

mapReader : (a -> b) -> Reader r a -> Reader r b
mapReader f = mapReaderT (asIdentity <<< f <<< runIdentity)

withReader : (r' -> r) -> Reader r a -> Reader r' a
withReader f m = withReaderT f m
