{-# OPTIONS --type-in-type #-}

module Control.Monad.Except.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
-- ExceptT
-------------------------------------------------------------------------------

record ExceptT (e : Set) (m : Set -> Set) (a : Set) : Set where
  constructor ExceptT:
  field runExceptT : m (e + a)

open ExceptT public

mapExceptT : (m (e + a) -> n (e' + b)) -> ExceptT e m a -> ExceptT e' n b
mapExceptT f m = ExceptT: (f (runExceptT m))

instance
  Functor-ExceptT : {{_ : Functor m}} -> Functor (ExceptT e m)
  Functor-ExceptT .map f = ExceptT: <<< map (map f) <<< runExceptT

  Applicative-ExceptT : {{_ : Monad m}} -> Applicative (ExceptT e m)
  Applicative-ExceptT .pure = ExceptT: <<< pure <<< Right
  Applicative-ExceptT ._<*>_ (ExceptT: mf) (ExceptT: mx) = ExceptT: do
    f <- mf
    case f of \ where
      (Left e) -> return (Left e)
      (Right g) -> do
        x <- mx
        case x of \ where
          (Left e) -> return (Left e)
          (Right y) -> return (Right (g y))

  Monad-ExceptT : {{_ : Monad m}} -> Monad (ExceptT e m)
  Monad-ExceptT ._>>=_ (ExceptT: m) k =
    ExceptT: (m >>= either (pure <<< Left) (runExceptT <<< k))

  MonadTrans-ExceptT : MonadTrans (ExceptT e)
  MonadTrans-ExceptT .lift = ExceptT: <<< map Right

  MonadThrow-ExceptT : {{_ : MonadThrow m}} -> MonadThrow (ExceptT e m)
  MonadThrow-ExceptT .throw = lift <<< throw

  MonadCatch-ExceptT : {{_ : MonadCatch m}} -> MonadCatch (ExceptT e m)
  MonadCatch-ExceptT .catch (ExceptT: m) k =
    ExceptT: $ catch m (runExceptT <<< k)

  MonadBracket-ExceptT : {{_ : MonadBracket m}} -> MonadBracket (ExceptT e m)
  MonadBracket-ExceptT .generalBracket acquire release use = ExceptT: do
    (eb , ec) <- generalBracket
      (runExceptT acquire)
      (\ eresource exitCase -> case eresource of \ where
        (Left e) -> return (Left e)
        (Right resource) -> case exitCase of \ where
          (ExitCaseSuccess (Right b)) ->
            runExceptT (release resource (ExitCaseSuccess b))
          (ExitCaseException e) ->
            runExceptT (release resource (ExitCaseException e))
          _ ->
            runExceptT (release resource ExitCaseAbort))
      (either (return <<< Left) (runExceptT <<< use))
    return do
      c <- ec
      b <- eb
      return (b , c)

  MonadReader-ExceptT : {{_ : MonadReader r m}} -> MonadReader r (ExceptT e m)
  MonadReader-ExceptT .ask = lift ask
  MonadReader-ExceptT .local f = mapExceptT (local f)

  MonadWriter-ExceptT : {{_ : MonadWriter w m}} -> MonadWriter w (ExceptT e m)
  MonadWriter-ExceptT .tell = lift <<< tell
  MonadWriter-ExceptT .listen = mapExceptT \ m -> do
    p <- listen m
    case p of \ where
      (a , w) -> pure $ (_, w) <$> a
  MonadWriter-ExceptT .pass = mapExceptT \ m -> pass do
    a <- m
    pure $ case a of \ where
      (Left e) -> (Left e , id)
      (Right (r , f)) -> (Right r , f)

  MonadState-ExceptT : {{_ : MonadState s m}} -> MonadState s (ExceptT e m)
  MonadState-ExceptT .state = lift <<< state

  MonadCont-ExceptT : {{_ : MonadCont m}} -> MonadCont (ExceptT e m)
  MonadCont-ExceptT .callCC f = ExceptT: $
    callCC \ c -> runExceptT (f (\ a -> ExceptT: $ c (Right a)))
