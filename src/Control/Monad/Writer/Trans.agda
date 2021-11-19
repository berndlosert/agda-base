module Control.Monad.Writer.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception
open import Control.Monad.Cont.Class
open import Control.Monad.Error.Class
open import Control.Monad.IO.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Trans.Class public
open Control.Monad.Writer.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s w w' : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- WriterT
-------------------------------------------------------------------------------

record WriterT (w : Set) (m : Set -> Set) (a : Set) : Set where
  constructor aWriterT
  field runWriterT : m (Pair w a)

open WriterT public

execWriterT : {{Functor m}} -> WriterT w m a -> m w
execWriterT = map fst <<< runWriterT

mapWriterT : (m (Pair w a) -> n (Pair w' b))
  -> WriterT w m a -> WriterT w' n b
mapWriterT f = aWriterT <<< f <<< runWriterT

instance
  Functor-WriterT : {{Functor m}} -> Functor (WriterT w m)
  Functor-WriterT .map = mapWriterT <<< map <<< map

  Applicative-WriterT : {{Monoid w}} -> {{Applicative m}}
    -> Applicative (WriterT w m)
  Applicative-WriterT .pure = aWriterT <<< pure <<< (mempty ,_)
  Applicative-WriterT ._<*>_ fs xs =
      aWriterT (| k (runWriterT fs) (runWriterT xs) |)
    where
      k : _
      k (w , f) (w' , x) = (w <> w' , f x)

  Alternative-WriterT : {{Monoid w}} -> {{Alternative m}}
    -> Alternative (WriterT w m)
  Alternative-WriterT .azero = aWriterT azero
  Alternative-WriterT ._<|>_ l r = aWriterT (runWriterT l <|> runWriterT r)

  Monad-WriterT : {{Monoid w}} -> {{Monad m}} -> Monad (WriterT w m)
  Monad-WriterT ._>>=_ m k = aWriterT do
    (w , x) <- runWriterT m
    (w' , y) <- runWriterT (k x)
    pure (w <> w' , y)

  MonadTrans-WriterT : {{Monoid w}} -> MonadTrans (WriterT w)
  MonadTrans-WriterT .lift m = aWriterT do
    x <- m
    pure (mempty , x)

  MonadWriter-WriterT : {{Monoid w}} -> {{Monad m}}
    -> MonadWriter w (WriterT w m)
  MonadWriter-WriterT .tell = aWriterT <<< pure <<< (_, tt)
  MonadWriter-WriterT .listen m = aWriterT do
    (w , x) <- runWriterT m
    pure (w , (w , x))
  MonadWriter-WriterT .pass m = aWriterT do
    (w , (f , x)) <- runWriterT m
    pure (f w , x)

  MonadReader-WriterT : {{Monoid w}} -> {{MonadReader r m}}
    -> MonadReader r (WriterT w m)
  MonadReader-WriterT .ask = lift ask
  MonadReader-WriterT .local = mapWriterT <<< local

  MonadState-WriterT : {{Monoid w}} -> {{MonadState s m}}
    -> MonadState s (WriterT w m)
  MonadState-WriterT .state = lift <<< state

  MonadThrow-WriterT : {{Monoid w}} -> {{MonadThrow m}}
    -> MonadThrow (WriterT w m)
  MonadThrow-WriterT .throw = lift <<< throw

  MonadCatch-WriterT : {{Monoid w}} -> {{MonadCatch m}}
    -> MonadCatch (WriterT w m)
  MonadCatch-WriterT ._catch_ m h = aWriterT $
    (runWriterT m) catch (runWriterT <<< h)

  MonadCont-WriterT : {{Monoid w}} -> {{MonadCont m}}
    -> MonadCont (WriterT w m)
  MonadCont-WriterT .callCC f = aWriterT $
    callCC \ c -> (runWriterT <<< f) (aWriterT <<< c <<< (mempty ,_))

  MonadError-WriterT : {{Monoid w}}
    -> {{MonadError e m}} -> MonadError e (WriterT w m)
  MonadError-WriterT .raiseError = lift <<< raiseError
  MonadError-WriterT .handleError m h = aWriterT $
    handleError (runWriterT m) (runWriterT <<< h)
