{-# OPTIONS --type-in-type #-}

module Control.Monad.Either.Trans where

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
-- EitherT
-------------------------------------------------------------------------------

abstract
  EitherT : (e : Type) (m : Type -> Type) (a : Type) -> Type
  EitherT e m a = m (e + a)

  mkEitherT : m (e + a) -> EitherT e m a
  mkEitherT = id

  runEitherT : EitherT e m a -> m (e + a)
  runEitherT = id

mapEitherT : (m (e + a) -> n (e' + b)) -> EitherT e m a -> EitherT e' n b
mapEitherT f m = mkEitherT (f (runEitherT m))

withEitherT : {{Functor m}} -> (e -> e') -> EitherT e m a -> EitherT e' m a
withEitherT f t = mkEitherT $ map (lmap f) (runEitherT t)

instance
  Functor-EitherT : {{Functor m}} -> Functor (EitherT e m)
  Functor-EitherT .map f = mkEitherT <<< map (map f) <<< runEitherT

  Applicative-EitherT : {{Monad m}} -> Applicative (EitherT e m)
  Applicative-EitherT .pure = mkEitherT <<< pure <<< pure
  Applicative-EitherT ._<*>_ f x =
    mkEitherT (| _<*>_ (runEitherT f) (runEitherT x) |)

  Alternative-EitherT : {{Monoid e}} -> {{Monad m}}
    -> Alternative (EitherT e m)
  Alternative-EitherT .empty = mkEitherT $ pure (Left neutral)
  Alternative-EitherT ._<|>_ l r =
    mkEitherT $ runEitherT l >>= \ where
      (Left e) -> map (either (Left <<< (e <>_)) Right) (runEitherT r)
      (Right x) -> pure (Right x)

  Monad-EitherT : {{Monad m}} -> Monad (EitherT e m)
  Monad-EitherT ._>>=_ m k =
    mkEitherT (runEitherT m >>= either (pure <<< Left) (runEitherT <<< k))

  MonadTrans-EitherT : MonadTrans (EitherT e)
  MonadTrans-EitherT .lift = mkEitherT <<< map Right

  MonadThrow-EitherT : {{MonadThrow m}} -> MonadThrow (EitherT e m)
  MonadThrow-EitherT .throw = lift <<< throw

  MonadCatch-EitherT : {{MonadCatch m}} -> MonadCatch (EitherT e m)
  MonadCatch-EitherT .catch m k =
    mkEitherT $ catch (runEitherT m) (runEitherT <<< k)

  MonadBracket-EitherT : {{MonadBracket m}} -> MonadBracket (EitherT e m)
  MonadBracket-EitherT .generalBracket acquire release use = mkEitherT do
    (eb , ec) <- generalBracket
      (runEitherT acquire)
      (\ where
        (Left e) _ -> pure (Left e)
        (Right resource) (ExitCaseSuccess (Right b)) ->
          runEitherT (release resource (ExitCaseSuccess b))
        (Right resource) (ExitCaseException e) ->
          runEitherT (release resource (ExitCaseException e))
        (Right resource) _ ->
          runEitherT (release resource ExitCaseAbort))
      (either (pure <<< Left) (runEitherT <<< use))
    pure do
      c <- ec
      b <- eb
      pure (b , c)

  MonadReader-EitherT : {{MonadReader r m}} -> MonadReader r (EitherT e m)
  MonadReader-EitherT .ask = lift ask
  MonadReader-EitherT .local f = mapEitherT (local f)

  MonadWriter-EitherT : {{MonadWriter w m}} -> MonadWriter w (EitherT e m)
  MonadWriter-EitherT .tell = lift <<< tell
  MonadWriter-EitherT .listen = mapEitherT \ m -> do
    (w , x) <- listen m
    pure $ (w ,_) <$> x
  MonadWriter-EitherT .pass = mapEitherT \ m ->
    pass $ m >>= pure <<< either (pair (const id) Left) (bimap id Right)

  MonadState-EitherT : {{MonadState s m}} -> MonadState s (EitherT e m)
  MonadState-EitherT .state = lift <<< state

  MonadCont-EitherT : {{MonadCont m}} -> MonadCont (EitherT e m)
  MonadCont-EitherT .callCC f = mkEitherT $
    callCC \ c -> runEitherT (f $ mkEitherT <<< c <<< Right)
