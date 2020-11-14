{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --no-termination-check #-}

module Control.Monad.Iter.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Monad.Except.Class
open import Control.Monad.Free.Class
open import Control.Monad.IO.Class
open import Control.Monad.Morph
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Trans.Class public
open Data.Functor.Identity public

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

record IterT (m : Set -> Set) (a : Set) : Set where
  coinductive
  field runIterT : m (a + IterT m a)

open IterT public

Iter : Set -> Set
Iter = IterT Identity

delay : {{_ : Monad m}} -> IterT m a -> IterT m a
delay iter .runIterT = return (Right iter)

never : {{_ : Monad m}} -> IterT m a
never .runIterT = return (Right never)

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
retract : {{_ : Monad m}} -> IterT m a -> m a
retract iter = runIterT iter >>= either return retract

instance
  Functor-IterT : {{_ : Monad m}} -> Functor (IterT m)
  Functor-IterT .map f iter .runIterT = runIterT iter <#> \ where
    (Left x) -> Left (f x)
    (Right iter') -> Right (map f iter')

  Applicative-IterT : {{_ : Monad m}} -> Applicative (IterT m)
  Applicative-IterT .pure x .runIterT = return (Left x)
  Applicative-IterT ._<*>_ iter x .runIterT = caseM runIterT iter of \ where
    (Left f) -> runIterT (map f x)
    (Right iter') -> return (Right (iter' <*> x))

  Monad-IterT : {{_ : Monad m}} -> Monad (IterT m)
  Monad-IterT ._>>=_ iter k .runIterT = caseM runIterT iter of \ where
    (Left m) -> runIterT (k m)
    (Right iter') -> return (Right (iter' >>= k))

  Alternative-IterT : {{_ : Monad m}} -> Alternative (IterT m)
  Alternative-IterT .empty = never
  Alternative-IterT ._<|>_ l r .runIterT = do
    resultl <- runIterT l
    case resultl of \ where
      (Left _) -> return resultl
      (Right iter') -> do
        resultr <- runIterT r
        case resultr of \ where
          (Left _) -> return resultr
          (Right iter'') -> return (Right (iter' <|> iter''))

  MonadFree-IterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
  MonadFree-IterT .wrap (Identity: iter) = delay iter

  MFunctor-IterT : MFunctor IterT
  MFunctor-IterT .hoist t iter .runIterT =
    (map $ hoist t) <$> (t $ runIterT iter)

  MonadTrans-IterT : MonadTrans IterT
  MonadTrans-IterT .lift m .runIterT = map Left m

  MonadReader-IterT : {{_ : MonadReader r m}} -> MonadReader r (IterT m)
  MonadReader-IterT .ask = lift ask
  MonadReader-IterT .local f = hoist (local f)

  MonadWriter-IterT : {{_ : MonadWriter w m}} -> MonadWriter w (IterT m)
  MonadWriter-IterT .tell = lift <<< tell
  MonadWriter-IterT {w = w} {m = m} .listen {a = a} iter .runIterT =
      map concat' $ listen (map listen <$> runIterT iter)
    where
      concat' : (a + IterT m (a * w)) * w -> (a * w) + IterT m (a * w)
      concat' (Left x , w) = Left (x , w)
      concat' (Right y , w) = Right $ map (w <>_) <$> y
  MonadWriter-IterT {w = w} {m = m} .pass {a = a} iter .runIterT =
      pass' $ runIterT $ hoist clean $ listen iter
    where
      clean : forall {a} -> m a -> m a
      clean = pass <<< map (_, const mempty)

      c : Set
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

  MonadThrow-IterT : {{_ : MonadThrow e m}} -> MonadThrow e (IterT m)
  MonadThrow-IterT .throw = lift <<< throw

  MonadExcept-IterT : {{_ : MonadExcept e m}} -> MonadExcept e (IterT m)
  MonadExcept-IterT .catch iter f .runIterT =
    catch (map (flip catch f) <$> runIterT iter) (runIterT <<< f)
