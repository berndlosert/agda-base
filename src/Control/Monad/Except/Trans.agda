{-# OPTIONS --type-in-type #-}

module Control.Monad.Except.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Exception
open import Control.Monad.Cont.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e e' r s w : Type
    m n : Type -> Type

-------------------------------------------------------------------------------
-- ExceptT
-------------------------------------------------------------------------------

abstract
  ExceptT : (e : Type) (m : Type -> Type) (a : Type) -> Type
  ExceptT e m a = m (e + a)

  mkExceptT : m (e + a) -> ExceptT e m a
  mkExceptT = id

  runExceptT : ExceptT e m a -> m (e + a)
  runExceptT = id

mapExceptT : (m (e + a) -> n (e' + b)) -> ExceptT e m a -> ExceptT e' n b
mapExceptT f m = mkExceptT (f (runExceptT m))

withExceptT : {{Functor m}} -> (e -> e') -> ExceptT e m a -> ExceptT e' m a
withExceptT f t = mkExceptT $ map (lmap f) (runExceptT t)

instance
  Functor-ExceptT : {{Functor m}} -> Functor (ExceptT e m)
  Functor-ExceptT .map f = mkExceptT <<< map (map f) <<< runExceptT

  Applicative-ExceptT : {{Monad m}} -> Applicative (ExceptT e m)
  Applicative-ExceptT .pure = mkExceptT <<< pure <<< pure
  Applicative-ExceptT ._<*>_ f x =
    mkExceptT (| _<*>_ (runExceptT f) (runExceptT x) |)

  Alternative-ExceptT : {{Monoid e}} -> {{Monad m}}
    -> Alternative (ExceptT e m)
  Alternative-ExceptT .empty = mkExceptT $ pure (Left neutral)
  Alternative-ExceptT ._<|>_ l r =
    mkExceptT $ runExceptT l >>= \ where
      (Left e) -> map (either (Left <<< (e <>_)) Right) (runExceptT r)
      (Right x) -> pure (Right x)

  Monad-ExceptT : {{Monad m}} -> Monad (ExceptT e m)
  Monad-ExceptT ._>>=_ m k =
    mkExceptT (runExceptT m >>= either (pure <<< Left) (runExceptT <<< k))

  MonadTrans-ExceptT : MonadTrans (ExceptT e)
  MonadTrans-ExceptT .lift = mkExceptT <<< map Right

  MonadThrow-ExceptT : {{MonadThrow m}} -> MonadThrow (ExceptT e m)
  MonadThrow-ExceptT .throw = lift <<< throw

  MonadCatch-ExceptT : {{MonadCatch m}} -> MonadCatch (ExceptT e m)
  MonadCatch-ExceptT .catch m k =
    mkExceptT $ catch (runExceptT m) (runExceptT <<< k)

  MonadBracket-ExceptT : {{MonadBracket m}} -> MonadBracket (ExceptT e m)
  MonadBracket-ExceptT .generalBracket acquire release use = mkExceptT do
    (eb , ec) <- generalBracket
      (runExceptT acquire)
      (\ where
        (Left e) _ -> pure (Left e)
        (Right resource) (ExitCaseSuccess (Right b)) ->
          runExceptT (release resource (ExitCaseSuccess b))
        (Right resource) (ExitCaseException e) ->
          runExceptT (release resource (ExitCaseException e))
        (Right resource) _ ->
          runExceptT (release resource ExitCaseAbort))
      (either (pure <<< Left) (runExceptT <<< use))
    pure do
      c <- ec
      b <- eb
      pure (b , c)

  MonadReader-ExceptT : {{MonadReader r m}} -> MonadReader r (ExceptT e m)
  MonadReader-ExceptT .ask = lift ask
  MonadReader-ExceptT .local f = mapExceptT (local f)

  MonadWriter-ExceptT : {{MonadWriter w m}} -> MonadWriter w (ExceptT e m)
  MonadWriter-ExceptT .tell = lift <<< tell
  MonadWriter-ExceptT .listen = mapExceptT \ m -> do
    (w , x) <- listen m
    pure $ (w ,_) <$> x
  MonadWriter-ExceptT .pass = mapExceptT \ m ->
    pass $ m >>= pure <<< either (pair (const id) Left) (bimap id Right)

  MonadState-ExceptT : {{MonadState s m}} -> MonadState s (ExceptT e m)
  MonadState-ExceptT .state = lift <<< state

  MonadCont-ExceptT : {{MonadCont m}} -> MonadCont (ExceptT e m)
  MonadCont-ExceptT .callCC f = mkExceptT $
    callCC \ c -> runExceptT (f $ mkExceptT <<< c <<< Right)
