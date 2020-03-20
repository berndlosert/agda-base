{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Reader where

open import Control.Monad.Trans.Class
open import Prelude

private
  variable
    A B R R' : Set
    M N : Set -> Set

--------------------------------------------------------------------------------
-- MonadReader
--------------------------------------------------------------------------------

record MonadReader (R : Set) (M : Set -> Set) : Set where
  field
    {{monad}} : Monad M
    ask : M R
    local : (R -> R) -> M ~> M

  asks : (R -> A) -> M A
  asks f = do
    r <- ask
    return (f r)

open MonadReader {{...}} public

--------------------------------------------------------------------------------
-- ReaderT
--------------------------------------------------------------------------------

record ReaderT (R : Set) (M : Set -> Set) (A : Set) : Set where
  constructor readerT
  field runReaderT : R -> M A
open ReaderT public

mapReaderT : (M A -> N B) -> ReaderT R M A -> ReaderT R N B
mapReaderT f m = readerT $ f <<< runReaderT m

withReaderT : (R' -> R) -> ReaderT R M ~> ReaderT R' M
withReaderT f m = readerT $ runReaderT m <<< f

instance
  functorReaderT : {{_ : Functor M}} -> Functor (ReaderT R M)
  functorReaderT .map f = mapReaderT (map f)

  applicativeReaderT : {{_ : Applicative M}} -> Applicative (ReaderT R M)
  applicativeReaderT .pure = readerT <<< const <<< pure
  applicativeReaderT ._<*>_ f v = readerT $ \ r ->
    runReaderT f r <*> runReaderT v r

  monadReaderT : {{_ : Monad M}} -> Monad (ReaderT R M)
  monadReaderT ._>>=_ m k = readerT $ \ r -> do
    a <- runReaderT m r
    runReaderT (k a) r

  monadReaderReaderT : {{_ : Monad M}} -> MonadReader R (ReaderT R M)
  monadReaderReaderT .ask = readerT return
  monadReaderReaderT .local f = withReaderT f

  monadTransReaderT : MonadTrans (ReaderT R)
  monadTransReaderT .lift = readerT <<< const
  monadTransReaderT .transform = monadReaderT

--------------------------------------------------------------------------------
-- Reader
--------------------------------------------------------------------------------

Reader : Set -> Set -> Set
Reader R = ReaderT R Identity

runReader : Reader R A -> R -> A
runReader m = runIdentity <<< runReaderT m

mapReader : (A -> B) -> Reader R A -> Reader R B
mapReader f = mapReaderT (value <<< f <<< runIdentity)

withReader : (R' -> R) -> Reader R A -> Reader R' A
withReader f m = withReaderT f m
