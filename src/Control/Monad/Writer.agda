module Control.Monad.Writer where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Writer.Class
open import Control.Monad.Writer.Trans

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Writer.Class public
open Control.Monad.Writer.Trans public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b w w' : Type

-------------------------------------------------------------------------------
-- Writer
-------------------------------------------------------------------------------

Writer : Type -> Type -> Type
Writer w = WriterT w Identity

{-# DISPLAY WriterT w Identity = Writer w #-}

runWriter : Writer w a -> Tuple w a
runWriter = runIdentity <<< runWriterT

execWriter : Writer w a -> w
execWriter = fst <<< runWriter

mapWriter : (Tuple w a -> Tuple w' b) -> Writer w a -> Writer w' b
mapWriter = mapWriterT <<< map
