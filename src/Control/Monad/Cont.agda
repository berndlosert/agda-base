{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Cont.Class
open import Control.Monad.Cont.Trans
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Cont.Class public
open Control.Monad.Cont.Trans public
open Data.Functor.Identity public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b r r' : Set

-------------------------------------------------------------------------------
-- Cont
-------------------------------------------------------------------------------

Cont : Set -> Set -> Set
Cont r a = ContT r Identity a

{-# DISPLAY ContT r Identity = Cont r #-}

cont : ((a -> r) -> r) -> Cont r a
cont f = ContT: \ c -> toIdentity (f (runIdentity <<< c))

runCont : Cont r a -> (a -> r) -> r
runCont m k = runIdentity (runContT m (toIdentity <<< k))

evalCont : Cont r r -> r
evalCont = runIdentity <<< evalContT

mapCont : (r -> r) -> Cont r a -> Cont r a
mapCont = mapContT <<< map

withCont : ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b
withCont f = withContT ((toIdentity <<<_) <<< f <<< (runIdentity <<<_))

reset : Cont r r -> Cont r' r
reset = resetT

shift : ((a -> r) -> Cont r r) -> Cont r a
shift f = shiftT (f <<< (runIdentity <<<_))
