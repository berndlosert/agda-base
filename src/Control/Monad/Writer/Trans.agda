module Control.Monad.Writer.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
    a b e r s w w' : Type
    m n : Type -> Type

-------------------------------------------------------------------------------
-- WriterT
-------------------------------------------------------------------------------

record WriterT (w : Type) (m : Type -> Type) (a : Type) : Type where
  constructor asWriterT
  field runWriterT : m (Tuple w a)

open WriterT public

execWriterT : {{Functor m}} -> WriterT w m a -> m w
execWriterT = map fst <<< runWriterT

mapWriterT : (m (Tuple w a) -> n (Tuple w' b))
  -> WriterT w m a -> WriterT w' n b
mapWriterT f = asWriterT <<< f <<< runWriterT

instance
  Functor-WriterT : {{Functor m}} -> Functor (WriterT w m)
  Functor-WriterT .map = mapWriterT <<< map <<< map

  Applicative-WriterT : {{Monoid w}} -> {{Applicative m}}
    -> Applicative (WriterT w m)
  Applicative-WriterT .pure = asWriterT <<< pure <<< (mempty ,_)
  Applicative-WriterT ._<*>_ fs xs =
      asWriterT (| k (runWriterT fs) (runWriterT xs) |)
    where
      k : _
      k (v , f) (w , x) = (v <> w , f x)

  Alternative-WriterT : {{Monoid w}} -> {{Alternative m}}
    -> Alternative (WriterT w m)
  Alternative-WriterT .azero = asWriterT azero
  Alternative-WriterT ._<|>_ l r = asWriterT (runWriterT l <|> runWriterT r)

  Monad-WriterT : {{Monoid w}} -> {{Monad m}} -> Monad (WriterT w m)
  Monad-WriterT ._>>=_ m k = asWriterT do
    (v , x) <- runWriterT m
    (w , y) <- runWriterT (k x)
    pure (v <> w , y)

  MonadTrans-WriterT : {{Monoid w}} -> MonadTrans (WriterT w)
  MonadTrans-WriterT .lift m = asWriterT (| (mempty ,_) m |)

  MonadWriter-WriterT : {{Monoid w}} -> {{Monad m}}
    -> MonadWriter w (WriterT w m)
  MonadWriter-WriterT .tell = asWriterT <<< pure <<< (_, tt)

  MonadReader-WriterT : {{Monoid w}} -> {{MonadReader r m}}
    -> MonadReader r (WriterT w m)
  MonadReader-WriterT .ask = lift ask

  MonadState-WriterT : {{Monoid w}} -> {{MonadState s m}}
    -> MonadState s (WriterT w m)
  MonadState-WriterT .state = lift <<< state

  MonadCont-WriterT : {{Monoid w}} -> {{MonadCont m}}
    -> MonadCont (WriterT w m)
  MonadCont-WriterT .callCC f = asWriterT $
    callCC \ c -> (runWriterT <<< f) (asWriterT <<< c <<< (mempty ,_))

  MonadError-WriterT : {{Monoid w}}
    -> {{MonadError e m}} -> MonadError e (WriterT w m)
  MonadError-WriterT .throwError = lift <<< throwError

module _ {{_ : MonadWriter w m}} where

  listen : WriterT w m a -> m (Tuple w a)
  listen m = do
    (w , x) <- runWriterT m
    tell w
    pure (w , x)

  pass : WriterT w m (Tuple (w -> w) a) -> m a
  pass m = do
    (w , (f , x)) <- runWriterT m
    tell (f w)
    pure x

  listens : (w -> b) -> WriterT w m a -> m (Tuple a b)
  listens f m = do
    (w , x) <- listen m
    pure (x , f w)

  censor : (w -> w) -> WriterT w m a -> m a
  censor f m = pass (map (f ,_) m)