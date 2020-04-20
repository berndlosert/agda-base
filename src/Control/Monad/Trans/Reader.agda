{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Reader where

open import Prelude

open import Control.Monad.Trans.Class
  using (MonadTrans; lift; transform)

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
  constructor toReaderT
  field fromReaderT : R -> M A

open ReaderT public

mapReaderT : (M A -> N B) -> ReaderT R M A -> ReaderT R N B
mapReaderT f m = toReaderT $ f <<< fromReaderT m

withReaderT : (R' -> R) -> ReaderT R M ~> ReaderT R' M
withReaderT f m = toReaderT $ fromReaderT m <<< f

instance
  functorReaderT : {{_ : Functor M}} -> Functor (ReaderT R M)
  functorReaderT .map f = mapReaderT (map f)

  applicativeReaderT : {{_ : Applicative M}} -> Applicative (ReaderT R M)
  applicativeReaderT .pure = toReaderT <<< const <<< pure
  applicativeReaderT ._<*>_ f v = toReaderT $ \ r ->
    fromReaderT f r <*> fromReaderT v r

  monadReaderT : {{_ : Monad M}} -> Monad (ReaderT R M)
  monadReaderT ._>>=_ m k = toReaderT $ \ r -> do
    a <- fromReaderT m r
    fromReaderT (k a) r

  monadReaderReaderT : {{_ : Monad M}} -> MonadReader R (ReaderT R M)
  monadReaderReaderT .ask = toReaderT return
  monadReaderReaderT .local f = withReaderT f

  monadTransReaderT : MonadTrans (ReaderT R)
  monadTransReaderT .lift = toReaderT <<< const
  monadTransReaderT .transform = monadReaderT

--------------------------------------------------------------------------------
-- Reader
--------------------------------------------------------------------------------

Reader : Set -> Set -> Set
Reader R = ReaderT R Id

toReader : (R -> A) -> Reader R A
toReader f = toReaderT (f >>> toId)

fromReader : Reader R A -> R -> A
fromReader m = fromId <<< fromReaderT m

mapReader : (A -> B) -> Reader R A -> Reader R B
mapReader f = mapReaderT (toId <<< f <<< fromId)

withReader : (R' -> R) -> Reader R A -> Reader R' A
withReader f m = withReaderT f m
