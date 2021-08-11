{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Reader.Class
open import Control.Monad.Reader.Trans
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Reader.Class public
open Control.Monad.Reader.Trans public
open Data.Functor.Identity public

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

reader : (r -> a) -> Reader r a
reader f = readerT (Identity: <<< f)

runReader : Reader r a -> r -> a
runReader m = runIdentity <<< runReaderT m

mapReader : (a -> b) -> Reader r a -> Reader r b
mapReader f = mapReaderT (Identity: <<< f <<< runIdentity)

withReader : (r' -> r) -> Reader r a -> Reader r' a
withReader f m = withReaderT f m
