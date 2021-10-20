module Control.Monad.State.Trans where

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

open Control.Monad.State.Class public
open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s w : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- StateT
-------------------------------------------------------------------------------

record StateT (s : Set) (m : Set -> Set) (a : Set) : Set where
  constructor aStateT
  field runStateT : s -> m (Pair s a)

open StateT public

evalStateT : {{Monad m}} -> StateT s m a -> s -> m a
evalStateT m s = runStateT m s >>= snd >>> pure

execStateT : {{Monad m}} -> StateT s m a -> s -> m s
execStateT m s = runStateT m s >>= fst >>> pure

mapStateT : (m (Pair s a) -> n (Pair s b)) -> StateT s m a -> StateT s n b
mapStateT f m = aStateT (f <<< runStateT m)

withStateT : (s -> s) -> StateT s m a -> StateT s m a
withStateT f m = aStateT (runStateT m <<< f)

instance
  Functor-StateT : {{Functor m}} -> Functor (StateT s m)
  Functor-StateT .map f m = aStateT (map (map f) <<< runStateT m)

  Applicative-StateT : {{Monad m}} -> Applicative (StateT s m)
  Applicative-StateT .pure x = aStateT (pure <<< (_, x))
  Applicative-StateT ._<*>_ f x = aStateT \ s0 -> do
      (s1 , g) <- runStateT f s0
      (s2 , y) <- runStateT x s1
      pure (s2 , g y)

  Alternative-StateT : {{Alternative m}} -> {{Monad m}} ->
    Alternative (StateT s m)
  Alternative-StateT .azero = aStateT (const azero)
  Alternative-StateT ._<|>_ l r = aStateT \ s ->
    runStateT l s <|> runStateT r s

  Monad-StateT : {{Monad m}} -> Monad (StateT s m)
  Monad-StateT ._>>=_ m k = aStateT \ s0 -> do
    (s1 , x) <- runStateT m s0
    runStateT (k x) s1

  MonadTrans-StateT : MonadTrans (StateT s)
  MonadTrans-StateT .lift m = aStateT \ s -> do
    x <- m
    pure (s , x)

  MonadState-StateT : {{Monad m}} -> MonadState s (StateT s m)
  MonadState-StateT .state f = aStateT (pure <<< f)

  MonadReader-StateT : {{MonadReader r m}} -> MonadReader r (StateT s m)
  MonadReader-StateT .ask = lift ask
  MonadReader-StateT .local = mapStateT <<< local

  MonadWriter-StateT : {{MonadWriter w m}} -> MonadWriter w (StateT s m)
  MonadWriter-StateT .tell = lift <<< tell
  MonadWriter-StateT .listen m = aStateT \ s -> do
    (w , (s' , x)) <- listen (runStateT m s)
    pure $ (s' , (w , x))
  MonadWriter-StateT .pass m = aStateT \ s -> pass do
     (s' , (f , x)) <- runStateT m s
     pure $ (f , (s' , x))

  MonadIO-StateT : {{MonadIO m}} -> MonadIO (StateT s m)
  MonadIO-StateT .liftIO = lift <<< liftIO

  MonadThrow-StateT : {{MonadThrow m}} -> MonadThrow (StateT s m)
  MonadThrow-StateT .throw = lift <<< throw

  MonadCatch-StateT : {{MonadCatch m}} -> MonadCatch (StateT s m)
  MonadCatch-StateT .catch m h = aStateT \ s ->
    catch (runStateT m s) (\ e -> runStateT (h e) s)

  MonadCont-StateT : {{MonadCont m}} -> MonadCont (StateT s m)
  MonadCont-StateT .callCC f = aStateT \ s ->
    callCC \ c -> runStateT (f (\ x -> aStateT \ _ -> c (s , x))) s

  MonadError-StateT : {{MonadError e m}} -> MonadError e (StateT s m)
  MonadError-StateT .raiseError = lift <<< raiseError
  MonadError-StateT .handleError m h = aStateT \ s ->
    handleError (runStateT m s) (\ e -> runStateT (h e) s)
