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

record ExceptT (e : Type) (m : Type -> Type) (a : Type) : Type where
  constructor ExceptT:
  field runExceptT : m (e + a)

open ExceptT public

mapExceptT : (m (e + a) -> n (e' + b)) -> ExceptT e m a -> ExceptT e' n b
mapExceptT f m = ExceptT: (f (runExceptT m))

withExceptT : {{Functor m}} -> (e -> e') -> ExceptT e m a -> ExceptT e' m a
withExceptT f (ExceptT: t) = ExceptT: $ map (lmap f) t

instance
  Functor-ExceptT : {{Functor m}} -> Functor (ExceptT e m)
  Functor-ExceptT .map f = ExceptT: <<< map (map f) <<< runExceptT

  Applicative-ExceptT : {{Monad m}} -> Applicative (ExceptT e m)
  Applicative-ExceptT .pure = ExceptT: <<< pure <<< pure
  Applicative-ExceptT ._<*>_ (ExceptT: mf) (ExceptT: mx) =
    ExceptT: (| _<*>_ mf mx |)

  Alternative-ExceptT : {{Monoid e}} -> {{Monad m}}
    -> Alternative (ExceptT e m)
  Alternative-ExceptT .empty = ExceptT: $ pure (Left neutral)
  Alternative-ExceptT ._<|>_ (ExceptT: mx) (ExceptT: my) =
    ExceptT: $ mx >>= \ where
      (Left e) -> map (either (Left <<< (e <>_)) Right) my
      (Right x) -> pure (Right x)

  Monad-ExceptT : {{Monad m}} -> Monad (ExceptT e m)
  Monad-ExceptT ._>>=_ (ExceptT: m) k =
    ExceptT: (m >>= either (pure <<< Left) (runExceptT <<< k))

  MonadTrans-ExceptT : MonadTrans (ExceptT e)
  MonadTrans-ExceptT .lift = ExceptT: <<< map Right

  MonadThrow-ExceptT : {{MonadThrow m}} -> MonadThrow (ExceptT e m)
  MonadThrow-ExceptT .throw = lift <<< throw

  MonadCatch-ExceptT : {{MonadCatch m}} -> MonadCatch (ExceptT e m)
  MonadCatch-ExceptT .catch (ExceptT: m) k =
    ExceptT: $ catch m (runExceptT <<< k)

  MonadBracket-ExceptT : {{MonadBracket m}} -> MonadBracket (ExceptT e m)
  MonadBracket-ExceptT .generalBracket acquire release use = ExceptT: do
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
    (a , w) <- listen m
    pure $ (_, w) <$> a
  MonadWriter-ExceptT .pass = mapExceptT \ m ->
    pass $ m >>= pure <<< either (pair Left (const id)) (bimap Right id)

  MonadState-ExceptT : {{MonadState s m}} -> MonadState s (ExceptT e m)
  MonadState-ExceptT .state = lift <<< state

  MonadCont-ExceptT : {{MonadCont m}} -> MonadCont (ExceptT e m)
  MonadCont-ExceptT .callCC f = ExceptT: $
    callCC \ c -> runExceptT (f $ ExceptT: <<< c <<< Right)
