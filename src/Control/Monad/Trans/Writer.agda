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
  constructor aWriterT
  field runWriterT : M (A * W)

open WriterT public

execWriterT : {{_ : Monad M}} -> WriterT W M A -> M W
execWriterT m = do
  (_ , w) <- runWriterT m
  return w

mapWriterT : (M (A * W) -> N (B * W')) -> WriterT W M A -> WriterT W' N B
mapWriterT f m = aWriterT $ f (runWriterT m)

instance
  functorWriterT : {{_ : Functor M}} -> Functor (WriterT W M)
  functorWriterT .map f = mapWriterT $ map $ λ where (a , w) -> (f a , w)

  applicativeWriterT : {{_ : Monoid W}} {{_ : Applicative M}}
    -> Applicative (WriterT W M)
  applicativeWriterT .pure a = aWriterT $ pure (a , neutral)
  applicativeWriterT ._<*>_ (aWriterT f) (aWriterT v) = aWriterT $ (| k f v |)
    where
      k : _
      k (a , w) (b , w') = (a b , w <> w')

  monadWriterT : {{_ : Monoid W}} {{_ : Monad M}} -> Monad (WriterT W M)
  monadWriterT ._>>=_ m k = aWriterT $ do
    (a , w) <- runWriterT m
    (b , w') <- runWriterT (k a)
    return (b , w <> w')

  monadTransWriterT : {{_ : Monoid W}} -> MonadTrans (WriterT W)
  monadTransWriterT .lift m = aWriterT $ do
    a <- m
    return (a , neutral)
  monadTransWriterT .transform = monadWriterT

  monadWriterWriterT : {{_ : Monoid W}} {{_ : Monad M}}
    -> MonadWriter W (WriterT W M)
  monadWriterWriterT .tell w = aWriterT $ return (unit , w)
  monadWriterWriterT .listen m = aWriterT $ do
    (a , w) <- runWriterT m
    return ((a , w) , w)
  monadWriterWriterT .pass m = aWriterT $ do
    ((a , f) , w) <- runWriterT m
    return (a , f w)

--------------------------------------------------------------------------------
-- Writer
--------------------------------------------------------------------------------

Writer : Set -> Set -> Set
Writer W = WriterT W Identity

aWriter : A * W -> Writer W A
aWriter = aWriterT ∘ anIdentity

runWriter : Writer W A -> A * W
runWriter = runIdentity ∘ runWriterT

execWriter : Writer W A -> W
execWriter m = snd (runWriter m)

mapWriter : (A * W -> B * W') -> Writer W A -> Writer W' B
mapWriter = mapWriterT ∘ map
