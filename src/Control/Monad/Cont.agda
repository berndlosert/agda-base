module Control.Monad.Cont where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Instances using (Monad-Identity)
open import Control.Monad.Cont.Trans as ContT using (ContT)

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

cont : ((a -> r) -> r) -> Cont r a
cont f = ContT.asContT \ c -> asIdentity (f (runIdentity <<< c))

runCont : Cont r a -> (a -> r) -> r
runCont m k = runIdentity (ContT.runContT m (asIdentity <<< k))

evalCont : Cont r r -> r
evalCont k = runIdentity (ContT.evalContT k)

mapCont : (r -> r) -> Cont r a -> Cont r a
mapCont = ContT.mapContT <<< map

withCont : ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b
withCont f = ContT.withContT ((asIdentity <<<_) <<< f <<< (runIdentity <<<_))

reset : Cont r r -> Cont r' r
reset = ContT.resetT

shift : ((a -> r) -> Cont r r) -> Cont r a
shift f = ContT.shiftT (f <<< (runIdentity <<<_))
