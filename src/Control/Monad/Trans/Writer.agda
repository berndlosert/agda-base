{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Writer where

open import Prelude

open import Control.Monad.Trans.Class
  using (MonadTrans; lift; transform)

private
  variable
    A B W W' : Set
    M N : Set -> Set

--------------------------------------------------------------------------------
-- MonadWriter
--------------------------------------------------------------------------------

record MonadWriter (W : Set) (M : Set -> Set) : Set where
  field
    {{monoid}} : Monoid W
    {{monad}} : Monad M
    tell : W -> M Unit
    listen : M A -> M (A * W)
    pass : M (A * (W -> W)) -> M A

  writer : A * W -> M A
  writer (a , w) = do
    tell w
    return a

  listens : (W -> B) -> M A -> M (A * B)
  listens f m = do
    (a , w) <- listen m
    return (a , f w)

  censor : (W -> W) -> M ~> M
  censor f m = pass $ do
    a <- m
    return (a , f)

open MonadWriter {{...}} public

--------------------------------------------------------------------------------
-- WriterT
--------------------------------------------------------------------------------

record WriterT (W : Set) (M : Set -> Set) (A : Set) : Set where
  constructor toWriterT
  field fromWriterT : M (A * W)

open WriterT public

execWriterT : {{_ : Monad M}} -> WriterT W M A -> M W
execWriterT m = do
  (_ , w) <- fromWriterT m
  return w

mapWriterT : (M (A * W) -> N (B * W')) -> WriterT W M A -> WriterT W' N B
mapWriterT f m = toWriterT $ f (fromWriterT m)

instance
  functorWriterT : {{_ : Functor M}} -> Functor (WriterT W M)
  functorWriterT .map f = mapWriterT $ map $ \ where (a , w) -> (f a , w)

  applicativeWriterT : {{_ : Monoid W}} {{_ : Applicative M}}
    -> Applicative (WriterT W M)
  applicativeWriterT .pure a = toWriterT $ pure (a , mempty)
  applicativeWriterT ._<*>_ (toWriterT f) (toWriterT v) = toWriterT $ (| k f v |)
    where
      k : _
      k (a , w) (b , w') = (a b , w <> w')

  monadWriterT : {{_ : Monoid W}} {{_ : Monad M}} -> Monad (WriterT W M)
  monadWriterT ._>>=_ m k = toWriterT $ do
    (a , w) <- fromWriterT m
    (b , w') <- fromWriterT (k a)
    return (b , w <> w')

  monadTransWriterT : {{_ : Monoid W}} -> MonadTrans (WriterT W)
  monadTransWriterT .lift m = toWriterT $ do
    a <- m
    return (a , mempty)
  monadTransWriterT .transform = monadWriterT

  monadWriterWriterT : {{_ : Monoid W}} {{_ : Monad M}}
    -> MonadWriter W (WriterT W M)
  monadWriterWriterT .tell w = toWriterT $ return (unit , w)
  monadWriterWriterT .listen m = toWriterT $ do
    (a , w) <- fromWriterT m
    return ((a , w) , w)
  monadWriterWriterT .pass m = toWriterT $ do
    ((a , f) , w) <- fromWriterT m
    return (a , f w)

--------------------------------------------------------------------------------
-- Writer
--------------------------------------------------------------------------------

Writer : Set -> Set -> Set
Writer W = WriterT W Id

toWriter : A * W -> Writer W A
toWriter = toId >>> toWriterT

fromWriter : Writer W A -> A * W
fromWriter = fromId <<< fromWriterT

execWriter : Writer W A -> W
execWriter m = snd (fromWriter m)

mapWriter : (A * W -> B * W') -> Writer W A -> Writer W' B
mapWriter = mapWriterT <<< map
