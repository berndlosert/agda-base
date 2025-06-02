module Control.Monad.Iter.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Free.Class
open import Control.Monad.IO.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class
open import Data.Bifunctor

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

record IterT (m : Type -> Type) (a : Type) : Type where
  constructor asIterT
  field runIterT : m (Either a (IterT m a))

open IterT public

delay : {{Monad m}} -> IterT m a -> IterT m a
delay iter .runIterT = pure (right iter)

never : {{Monad m}} -> IterT m a
never = asIterT (pure (right never))

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
execIterT : {{Monad m}} -> IterT m a -> m a
execIterT iter = runIterT iter >>= either pure execIterT

-- Safer version of execIterT' that stops after n steps.
execIterT' : {{Monad m}} -> Nat -> IterT m a -> m (Maybe a)
execIterT' 0 _ = pure nothing
execIterT' (suc n) iter =
  caseM (runIterT iter) \ where
    (left x) -> pure (just x)
    (right iter1) -> execIterT' n iter1

hoistIterT : {{Monad n}}
  -> (forall {a} -> m a -> n a)
  -> IterT m a
  -> IterT n a
hoistIterT t iter = asIterT ((map $ hoistIterT t) <$> (t $ runIterT iter))

instance
  Functor-IterT : {{Monad m}} -> Functor (IterT m)
  Functor-IterT .map f iter =
    asIterT ((either (left <<< f) (right <<< map f)) <$> (runIterT iter))

  Applicative-IterT : {{Monad m}} -> Applicative (IterT m)
  Applicative-IterT .pure x = asIterT (pure (left x))
  Applicative-IterT ._<*>_ iter x = asIterT $
    caseM (runIterT iter) \ where
      (left f) -> runIterT (map f x)
      (right iter1) -> pure (right (iter1 <*> x))

  Monad-IterT : {{Monad m}} -> Monad (IterT m)
  Monad-IterT ._>>=_ iter k = asIterT $
    caseM (runIterT iter) \ where
      (left m) -> runIterT (k m)
      (right iter1) -> pure (right (iter1 >>= k))

  Alternative-IterT : {{Monad m}} -> Alternative (IterT m)
  Alternative-IterT .azero = never
  Alternative-IterT ._<|>_ l r = asIterT $
    caseM (runIterT l) \ where
      resl@(left _) -> pure resl
      (right l1) ->
        caseM (runIterT r) \ where
          resr@(left _) -> pure resr
          (right r1) -> pure (right (l1 <|> r1))

  MonadFree-IterT : {{Monad m}} -> MonadFree Identity (IterT m)
  MonadFree-IterT .wrap (asIdentity iter) = delay iter

  MonadTrans-IterT : MonadTrans IterT
  MonadTrans-IterT .lift m .runIterT = map left m

  MonadReader-IterT : {{MonadReader r m}} -> MonadReader r (IterT m)
  MonadReader-IterT .ask = lift ask

  MonadWriter-IterT : {{MonadWriter w m}} -> MonadWriter w (IterT m)
  MonadWriter-IterT .tell = lift <<< tell

  MonadState-IterT : {{MonadState s m}} -> MonadState s (IterT m)
  MonadState-IterT .state m = lift (state m)

  MonadIO-IterT : {{MonadIO m}} -> MonadIO (IterT m)
  MonadIO-IterT .liftIO = lift <<< liftIO
