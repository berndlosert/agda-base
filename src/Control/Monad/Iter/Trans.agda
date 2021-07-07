{-# OPTIONS --type-in-type --guardedness #-}

module Control.Monad.Iter.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
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
    a b e r s w : Type
    m n : Type -> Type

-------------------------------------------------------------------------------
-- IterT
-------------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
record IterT (m : Type -> Type) (a : Type) : Type where
  coinductive
  field runIterT : m (a + IterT m a)

open IterT public

delay : {{_ : Monad m}} -> IterT m a -> IterT m a
delay iter .runIterT = return (Right iter)

{-# NON_TERMINATING #-}
never : {{_ : Monad m}} -> IterT m a
never .runIterT = return (Right never)

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
{-# NON_TERMINATING #-}
execIterT : {{_ : Monad m}} -> IterT m a -> m a
execIterT iter = runIterT iter >>= either return execIterT

{-# NON_TERMINATING #-}
hoistIterT : {{_ : Monad n}}
  -> (forall {a} -> m a -> n a)
  -> IterT m a
  -> IterT n a
hoistIterT t iter .runIterT =
  (map $ hoistIterT t) <$> (t $ runIterT iter)

instance
  {-# NON_TERMINATING #-}
  Functor-IterT : {{_ : Monad m}} -> Functor (IterT m)
  Functor-IterT .map f iter .runIterT = flip map (runIterT iter) \ where
    (Left x) -> Left (f x)
    (Right iter') -> Right (map f iter')

  {-# NON_TERMINATING #-}
  Applicative-IterT : {{_ : Monad m}} -> Applicative (IterT m)
  Applicative-IterT .pure x .runIterT = return (Left x)
  Applicative-IterT ._<*>_ iter x .runIterT = runIterT iter >>= \ where
    (Left f) -> runIterT (map f x)
    (Right iter') -> return (Right (iter' <*> x))

  {-# NON_TERMINATING #-}
  Monad-IterT : {{_ : Monad m}} -> Monad (IterT m)
  Monad-IterT ._>>=_ iter k .runIterT = runIterT iter >>= \ where
    (Left m) -> runIterT (k m)
    (Right iter') -> return (Right (iter' >>= k))

  {-# NON_TERMINATING #-}
  Alternative-IterT : {{_ : Monad m}} -> Alternative (IterT m)
  Alternative-IterT .empty = never
  Alternative-IterT ._<|>_ l r .runIterT = do
    resultl <- runIterT l
    case resultl of \ where
      (Left _) -> return resultl
      (Right l') -> do
        resultr <- runIterT r
        case resultr of \ where
          (Left _) -> return resultr
          (Right r') -> return $ Right (l' <|> r')

  MonadFree-IterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
  MonadFree-IterT .wrap (Identity: iter) = delay iter

  MonadTrans-IterT : MonadTrans IterT
  MonadTrans-IterT .lift m .runIterT = map Left m

  MonadReader-IterT : {{_ : MonadReader r m}} -> MonadReader r (IterT m)
  MonadReader-IterT .ask = lift ask
  MonadReader-IterT .local f = hoistIterT (local f)

  {-# NON_TERMINATING #-}
  MonadWriter-IterT : {{_ : MonadWriter w m}} -> MonadWriter w (IterT m)
  MonadWriter-IterT .tell = lift <<< tell

  MonadWriter-IterT {w = w} {m = m} .listen {a = a} iter .runIterT =
      map concat' $ listen (map listen <$> runIterT iter)
    where
      c : Type
      c = a * w

      concat' : (a + IterT m c) * w -> c + IterT m c
      concat' (Left x , w) = Left (x , w)
      concat' (Right y , w) = Right $ map (w <>_) <$> y

  MonadWriter-IterT {w = w} {m = m} .pass {a = a} iter .runIterT =
      pass' $ runIterT $ hoistIterT clean $ listen iter
    where
      clean : forall {a} -> m a -> m a
      clean = pass <<< map (_, const neutral)

      c : Type
      c = a * (w -> w) * w

      pass' : m (c + IterT m c) -> m (a + IterT m a)
      g : (c + IterT m c) -> m (a + IterT m a)

      pass' = join <<< map g

      g (Left (x , f , w)) = tell (f w) >> return (Left x)
      g (Right iter') =
        return (Right (\ where .runIterT -> pass' (runIterT iter')))

  MonadState-IterT : {{_ : MonadState s m}} -> MonadState s (IterT m)
  MonadState-IterT .state m = lift (state m)

  MonadIO-IterT : {{_ : MonadIO m}} -> MonadIO (IterT m)
  MonadIO-IterT .liftIO = lift <<< liftIO

  MonadThrow-IterT : {{_ : MonadThrow m}} -> MonadThrow (IterT m)
  MonadThrow-IterT .throw = lift <<< throw

  {-# NON_TERMINATING #-}
  MonadCatch-IterT : {{_ : MonadCatch m}} -> MonadCatch (IterT m)
  MonadCatch-IterT .catch iter f .runIterT =
    catch (map (flip catch f) <$> runIterT iter) (runIterT <<< f)
