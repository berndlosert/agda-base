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
    a b e e' r s w : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- EitherT
-------------------------------------------------------------------------------

record EitherT (e : Set) (m : Set -> Set) (a : Set) : Set where
  constructor toEitherT
  field runEitherT : m (Either e a)

open EitherT public

mapEitherT : (m (Either e a) -> n (Either e' b)) -> EitherT e m a -> EitherT e' n b
mapEitherT f m = toEitherT (f (runEitherT m))

withEitherT : {{Functor m}} -> (e -> e') -> EitherT e m a -> EitherT e' m a
withEitherT f t = toEitherT $ map (lmap f) (runEitherT t)

instance
  Functor-EitherT : {{Functor m}} -> Functor (EitherT e m)
  Functor-EitherT .map f = toEitherT <<< map (map f) <<< runEitherT

  Applicative-EitherT : {{Monad m}} -> Applicative (EitherT e m)
  Applicative-EitherT .pure = toEitherT <<< pure <<< pure
  Applicative-EitherT ._<*>_ f x =
    toEitherT (| _<*>_ (runEitherT f) (runEitherT x) |)

  Alternative-EitherT : {{Monoid e}} -> {{Monad m}}
    -> Alternative (EitherT e m)
  Alternative-EitherT .empty = toEitherT $ pure (left neutral)
  Alternative-EitherT ._<|>_ l r =
    toEitherT $ runEitherT l >>= \ where
      (left e) -> map (either (left <<< (e <>_)) right) (runEitherT r)
      (right x) -> pure (right x)

  Monad-EitherT : {{Monad m}} -> Monad (EitherT e m)
  Monad-EitherT ._>>=_ m k =
    toEitherT (runEitherT m >>= either (pure <<< left) (runEitherT <<< k))

  MonadTrans-EitherT : MonadTrans (EitherT e)
  MonadTrans-EitherT .lift = toEitherT <<< map right

  MonadThrow-EitherT : {{MonadThrow m}} -> MonadThrow (EitherT e m)
  MonadThrow-EitherT .throw = lift <<< throw

  MonadCatch-EitherT : {{MonadCatch m}} -> MonadCatch (EitherT e m)
  MonadCatch-EitherT .catch m k =
    toEitherT $ catch (runEitherT m) (runEitherT <<< k)

  MonadBracket-EitherT : {{MonadBracket m}} -> MonadBracket (EitherT e m)
  MonadBracket-EitherT .generalBracket acquire release use = toEitherT do
    (eb , ec) <- generalBracket
      (runEitherT acquire)
      (\ where
        (left e) _ -> pure (left e)
        (right resource) (ExitCaseSuccess (right b)) ->
          runEitherT (release resource (ExitCaseSuccess b))
        (right resource) (ExitCaseException e) ->
          runEitherT (release resource (ExitCaseException e))
        (right resource) _ ->
          runEitherT (release resource ExitCaseAbort))
      (either (pure <<< left) (runEitherT <<< use))
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
    pass $ m >>= pure <<< either (pair (const id) left) (bimap id right)

  MonadState-EitherT : {{MonadState s m}} -> MonadState s (EitherT e m)
  MonadState-EitherT .state = lift <<< state

  MonadCont-EitherT : {{MonadCont m}} -> MonadCont (EitherT e m)
  MonadCont-EitherT .callCC f = toEitherT $
    callCC \ c -> runEitherT (f $ toEitherT <<< c <<< right)
