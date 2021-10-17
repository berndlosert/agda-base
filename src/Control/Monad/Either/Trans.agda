{-# OPTIONS --type-in-type #-}

module Control.Monad.Either.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception
open import Control.Monad.Cont.Class
open import Control.Monad.Error.Class
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
  constructor anEitherT
  field runEitherT : m (Either e a)

open EitherT public

mapEitherT : (m (Either e a) -> n (Either e' b)) -> EitherT e m a -> EitherT e' n b
mapEitherT f m = anEitherT (f (runEitherT m))

withEitherT : {{Functor m}} -> (e -> e') -> EitherT e m a -> EitherT e' m a
withEitherT f t = anEitherT $ map (lmap f) (runEitherT t)

instance
  Functor-EitherT : {{Functor m}} -> Functor (EitherT e m)
  Functor-EitherT .map f = anEitherT <<< map (map f) <<< runEitherT

  Applicative-EitherT : {{Monad m}} -> Applicative (EitherT e m)
  Applicative-EitherT .pure = anEitherT <<< pure <<< pure
  Applicative-EitherT ._<*>_ f x =
    anEitherT (| runEitherT f <*> runEitherT x |)

  Alternative-EitherT : {{Monoid e}} -> {{Monad m}}
    -> Alternative (EitherT e m)
  Alternative-EitherT .azero = anEitherT $ pure (left mempty)
  Alternative-EitherT ._<|>_ l r = anEitherT do
    resl <- runEitherT l
    case resl of \ where
      (left el) -> do
        resr <- runEitherT r
        pure $ case resr of \ where
          (left er) -> left (el <> er)
          (right x) -> right x
      (right x) -> pure $ right x

  Monad-EitherT : {{Monad m}} -> Monad (EitherT e m)
  Monad-EitherT ._>>=_ m k =
    anEitherT (runEitherT m >>= either (pure <<< left) (runEitherT <<< k))

  MonadTrans-EitherT : MonadTrans (EitherT e)
  MonadTrans-EitherT .lift = anEitherT <<< map right

  MonadThrow-EitherT : {{MonadThrow m}} -> MonadThrow (EitherT e m)
  MonadThrow-EitherT .throw = lift <<< throw

  MonadCatch-EitherT : {{MonadCatch m}} -> MonadCatch (EitherT e m)
  MonadCatch-EitherT .catch m k = anEitherT $
    catch (runEitherT m) (runEitherT <<< k)

  MonadBracket-EitherT : {{MonadBracket m}} -> MonadBracket (EitherT e m)
  MonadBracket-EitherT .generalBracket acquire release use = anEitherT do
    (eb , ec) <- generalBracket
      (runEitherT acquire)
      (\ where
        (left e) _ -> pure (left e)
        (right resource) (exitCaseSuccess (right b)) ->
          runEitherT (release resource (exitCaseSuccess b))
        (right resource) (exitCaseException e) ->
          runEitherT (release resource (exitCaseException e))
        (right resource) _ ->
          runEitherT (release resource exitCaseAbort))
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
  MonadCont-EitherT .callCC f = anEitherT $
    callCC \ c -> runEitherT (f $ anEitherT <<< c <<< right)

  MonadError-EitherT : {{Monad m}} -> MonadError e (EitherT e m)
  MonadError-EitherT .raiseError = anEitherT <<< pure <<< left
  MonadError-EitherT .handleError m h = anEitherT do
    res <- runEitherT m
    case res of \ where
      (left e) -> runEitherT (h e)
      (right x) -> pure (right x)
