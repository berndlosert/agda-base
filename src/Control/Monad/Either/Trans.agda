module Control.Monad.Either.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Cont.Class
open import Control.Monad.Error.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class
open import Data.Bifunctor
open import Data.String.Show

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c e e' r s w : Type
    m n : Type -> Type

-------------------------------------------------------------------------------
-- EitherT
-------------------------------------------------------------------------------

record EitherT (e : Type) (m : Type -> Type) (a : Type) : Type where
  constructor asEitherT
  field runEitherT : m (Either e a)

open EitherT public

eitherT : {{Monad m}} -> (e -> m b) -> (a -> m b) -> EitherT e m a -> m b
eitherT f g m = runEitherT m >>= either f g

fromEitherT : {{Monad m}} -> EitherT e m a -> (e -> m a) -> m a
fromEitherT m h = eitherT h pure m

mapEitherT : (m (Either e a) -> n (Either e' b)) -> EitherT e m a -> EitherT e' n b
mapEitherT f m = asEitherT (f (runEitherT m))

withEitherT : {{Functor m}} -> (e -> e') -> EitherT e m a -> EitherT e' m a
withEitherT f t = asEitherT $ lmap f <$> runEitherT t

instance
  Show-EitherT : {{Show (m (Either e a))}} -> Show (EitherT e m a)
  Show-EitherT .show = showDefault
  Show-EitherT .showsPrec prec (asEitherT m) = showsUnaryWith showsPrec "asEitherT" prec m

  Functor-EitherT : {{Functor m}} -> Functor (EitherT e m)
  Functor-EitherT .map f = asEitherT <<< map (map f) <<< runEitherT

  Applicative-EitherT : {{Monad m}} -> Applicative (EitherT e m)
  Applicative-EitherT .pure = asEitherT <<< pure <<< pure
  Applicative-EitherT ._<*>_ f x =
    asEitherT (| runEitherT f <*> runEitherT x |)

  Alternative-EitherT : {{Monoid e}} -> {{Monad m}}
    -> Alternative (EitherT e m)
  Alternative-EitherT .azero = asEitherT (pure (left mempty))
  Alternative-EitherT ._<|>_ l r = asEitherT $
    caseM (runEitherT l) \ where
      (left el) ->
        caseM (runEitherT r) \ where
          (left er) -> pure (left (el <> er))
          (right x) -> pure (right x)
      (right x) -> pure (right x)

  Monad-EitherT : {{Monad m}} -> Monad (EitherT e m)
  Monad-EitherT ._>>=_ m k =
    asEitherT (runEitherT m >>= either (pure <<< left) (runEitherT <<< k))

  MonadTrans-EitherT : MonadTrans (EitherT e)
  MonadTrans-EitherT .lift = asEitherT <<< map right

  MonadReader-EitherT : {{MonadReader r m}} -> MonadReader r (EitherT e m)
  MonadReader-EitherT .ask = lift ask

  MonadWriter-EitherT : {{MonadWriter w m}} -> MonadWriter w (EitherT e m)
  MonadWriter-EitherT .tell = lift <<< tell

  MonadState-EitherT : {{MonadState s m}} -> MonadState s (EitherT e m)
  MonadState-EitherT .state = lift <<< state

  MonadCont-EitherT : {{MonadCont m}} -> MonadCont (EitherT e m)
  MonadCont-EitherT .callCC f = asEitherT $
    callCC \ c -> runEitherT (f $ asEitherT <<< c <<< right)

  MonadError-EitherT : {{Monad m}} -> MonadError e (EitherT e m)
  MonadError-EitherT .throwError = asEitherT <<< pure <<< left