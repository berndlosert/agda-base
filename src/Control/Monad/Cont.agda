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
    a b r r' : Type

-------------------------------------------------------------------------------
-- Cont
-------------------------------------------------------------------------------

Cont : Type -> Type -> Type
Cont r a = ContT r Identity a

{-# DISPLAY ContT r Identity = Cont r #-}

mkCont : ((a -> r) -> r) -> Cont r a
mkCont f = mkContT \ c -> Identity: (f (runIdentity <<< c))

runCont : Cont r a -> (a -> r) -> r
runCont m k = runIdentity (runContT m (Identity: <<< k))

evalCont : Cont r r -> r
evalCont = runIdentity <<< evalContT

mapCont : (r -> r) -> Cont r a -> Cont r a
mapCont = mapContT <<< map

withCont : ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b
withCont f = withContT ((Identity: <<<_) <<< f <<< (runIdentity <<<_))

reset : Cont r r -> Cont r' r
reset = resetT

shift : ((a -> r) -> Cont r r) -> Cont r a
shift f = shiftT (f <<< (runIdentity <<<_))
