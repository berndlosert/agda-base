{-# OPTIONS --type-in-type #-}

module Control.Monad.Iter.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception
open import Control.Monad.Free.Class
open import Control.Monad.IO.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s w : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- IterT
-------------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
record IterT (m : Set -> Set) (a : Set) : Set where
  constructor toIterT
  field runIterT : m (Either a (IterT m a))

open IterT public

delay : {{Monad m}} -> IterT m a -> IterT m a
delay iter .runIterT = pure (right iter)

never : {{Monad m}} -> IterT m a
never = fix \ where
  never -> toIterT $ pure (right never)

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
execIterT : {{Monad m}} -> IterT m a -> m a
execIterT = fix \ where
  go iter -> runIterT iter >>= either pure go

hoistIterT : {{Monad n}}
  -> (forall {a} -> m a -> n a)
  -> IterT m a
  -> IterT n a
hoistIterT = fix \ where
  go t iter -> toIterT ((map $ go t) <$> (t $ runIterT iter))

instance
  Functor-IterT : {{Monad m}} -> Functor (IterT m)
  Functor-IterT .map = fix \ where
    go f iter ->
      toIterT $ map (either (left <<< f) (right <<< go f)) (runIterT iter)

  Applicative-IterT : {{Monad m}} -> Applicative (IterT m)
  Applicative-IterT .pure x = toIterT $ pure (left x)
  Applicative-IterT ._<*>_ = fix \ where
    go iter x -> toIterT do
      res <- runIterT iter
      case res of \ where
        (left f) -> runIterT (map f x)
        (right iter') -> pure (right (go iter' x))

  Monad-IterT : {{Monad m}} -> Monad (IterT m)
  Monad-IterT ._>>=_ = fix \ where
    go iter k -> toIterT do
      res <- runIterT iter
      case res of \ where
        (left m) -> runIterT (k m)
        (right iter') -> pure (right (go iter' k))

  Alternative-IterT : {{Monad m}} -> Alternative (IterT m)
  Alternative-IterT .azero = never
  Alternative-IterT ._<|>_ = fix \ where
    go l r -> toIterT do
      resl <- runIterT l
      case resl of \ where
        (left _) -> pure resultl
        (right l') -> do
          resr <- runIterT r
          case resr of \ where
            (left _) -> pure resr
            (right r') -> pure $ right (go l' r')

  MonadFree-IterT : {{Monad m}} -> MonadFree Identity (IterT m)
  MonadFree-IterT .wrap (toIdentity iter) = delay iter

  MonadTrans-IterT : MonadTrans IterT
  MonadTrans-IterT .lift m .runIterT = map left m

  MonadReader-IterT : {{MonadReader r m}} -> MonadReader r (IterT m)
  MonadReader-IterT .ask = lift ask
  MonadReader-IterT .local f = hoistIterT (local f)

  MonadWriter-IterT : {{MonadWriter w m}} -> MonadWriter w (IterT m)
  MonadWriter-IterT .tell = lift <<< tell
  MonadWriter-IterT {w = w} {m = m} .listen {a = a} = fix \ where
      go iter -> toIterT $ map concat' $ listen (map go <$> runIterT iter)
    where
      c : Set
      c = Pair w a

      concat' : Pair w (Either a (IterT m c)) -> Either c (IterT m c)
      concat' (w , left x) = left (w , x)
      concat' (w , right y) = right $ lmap (w <>_) <$> y

  MonadWriter-IterT {w = w} {m = m} .pass {a = a} iter .runIterT =
      pass' $ runIterT $ hoistIterT clean $ listen iter
    where
      clean : forall {a} -> m a -> m a
      clean = pass <<< map (const mempty ,_)

      c : Set
      c = Pair w (Pair (w -> w) a)

      g : (Either c (IterT m c)) -> m (Either a (IterT m a))
      g = fix \ where
        go (left (w , (f , x))) -> tell (f w) >> pure (left x)
        go (right iter') ->
          pure (right (toIterT $ (join <<< map go) (runIterT iter')))

      pass' : m (Either c (IterT m c)) -> m (Either a (IterT m a))
      pass' = join <<< map g

  MonadState-IterT : {{MonadState s m}} -> MonadState s (IterT m)
  MonadState-IterT .state m = lift (state m)

  MonadIO-IterT : {{MonadIO m}} -> MonadIO (IterT m)
  MonadIO-IterT .liftIO = lift <<< liftIO

  MonadThrow-IterT : {{MonadThrow m}} -> MonadThrow (IterT m)
  MonadThrow-IterT .throw = lift <<< throw

  MonadCatch-IterT : {{MonadCatch m}} -> MonadCatch (IterT m)
  MonadCatch-IterT .catch = fix \ where
    go iter f -> toIterT $
      catch (map (flip go f) <$> runIterT iter) (runIterT <<< f)
