{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Writer.Class
open import Control.Monad.Writer.Trans
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Writer.Class public
open Control.Monad.Writer.Trans public
open Data.Functor.Identity public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b w w' : Set

-------------------------------------------------------------------------------
-- Writer
-------------------------------------------------------------------------------

Writer : Set -> Set -> Set
Writer w = WriterT w Identity

{-# DISPLAY WriterT w Identity = Writer w #-}

runWriter : Writer w a -> Pair w a
runWriter = runIdentity <<< runWriterT

execWriter : Writer w a -> w
execWriter = fst <<< runWriter

mapWriter : (Pair w a -> Pair w' b) -> Writer w a -> Writer w' b
mapWriter = mapWriterT <<< map
