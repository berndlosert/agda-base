{-# OPTIONS --type-in-type #-}

module Control.Exception where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c e : Type

-------------------------------------------------------------------------------
-- Exception, SomeException, IOException
-------------------------------------------------------------------------------

postulate
  Exception : Type -> Type
  SomeException : Type
  IOException : Type

  toException : {{Exception e}} -> e -> SomeException
  fromException : {{Exception e}} -> SomeException -> Maybe e
  displayException : {{Exception e}} -> e -> String

-------------------------------------------------------------------------------
-- MonadThrow
-------------------------------------------------------------------------------

record MonadThrow (m : Type -> Type) : Type where
  field
    overlap {{Monad-super}} : Monad m
    throw : {{Exception e}} -> e -> m a

open MonadThrow {{...}} public

-------------------------------------------------------------------------------
-- MonadCatch
-------------------------------------------------------------------------------

record MonadCatch (m : Type -> Type) : Type where
  field
    overlap {{MonadThrow-super}} : MonadThrow m
    catch : {{Exception e}} -> m a -> (e -> m a) -> m a

  catchJust : {{Exception e}} -> (e -> Maybe b) -> m a -> (b -> m a) -> m a
  catchJust p ma handler = catch ma \ e -> maybe (throw e) handler (p e)

  handle : {{Exception e}} -> (e -> m a) -> m a -> m a
  handle = flip catch

  handleJust : {{Exception e}} -> (e -> Maybe b) -> (b -> m a) -> m a -> m a
  handleJust = flip <<< catchJust

  try : {{Exception e}} -> m a -> m (e + a)
  try ma = catch (map Right ma) (pure <<< Left)

  tryJust : {{Exception e}} -> (e -> Maybe b) -> m a -> m (b + a)
  tryJust p ma = try ma >>= \ where
    (Right v) -> return (Right v)
    (Left e) -> maybe (throw e) (return <<< Left) (p e)

open MonadCatch {{...}} public

-------------------------------------------------------------------------------
-- MonadBracket
-------------------------------------------------------------------------------

data ExitCase (a : Type) : Type where
  ExitCaseSuccess : a -> ExitCase a
  ExitCaseException : SomeException -> ExitCase a
  ExitCaseAbort : ExitCase a

record MonadBracket (m : Type -> Type) : Type where
  field
    overlap {{Monad-super}} : Monad m
    generalBracket : m a -> (a -> ExitCase b -> m c) -> (a -> m b) -> m (b * c)

  bracket : m a -> (a -> m c) -> (a -> m b) -> m b
  bracket acquire release =
    map fst <<< generalBracket acquire (\ a _ -> release a)

  bracket' : m a -> m c -> m b -> m b
  bracket' before after action = bracket before (const after) (const action)

  bracketOnError : m a -> (a -> m c) -> (a -> m b) -> m b
  bracketOnError acquire release =
    map fst <<< generalBracket acquire \ where
      _ (ExitCaseSuccess _) -> return unit
      a _ -> do
        release a
        return unit

  onError : m a -> m b -> m a
  onError action handler =
    bracketOnError (return unit) (const handler) (const action)

  finally : m a -> m b -> m a
  finally action finalizer = bracket' (return unit) finalizer action

open MonadBracket {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

postulate
  instance
    Exception-SomeException : Exception SomeException
    Exception-IOException : Exception IOException

private
  postulate
    throwIO : {{Exception e}} -> e -> IO a
    catchIO : {{Exception e}} -> IO a -> (e -> IO a) -> IO a
    generalBracketIO : IO a -> (a -> ExitCase b -> IO c)
      -> (a -> IO b) -> IO (b * c)

instance
  MonadThrow-IO : MonadThrow IO
  MonadThrow-IO .throw = throwIO

  MonadCatch-IO : MonadCatch IO
  MonadCatch-IO .catch = catchIO

  MonadBracket-IO : MonadBracket IO
  MonadBracket-IO .generalBracket = generalBracketIO

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC
  import Control.Exception
  import Data.Text (pack)

  data ExceptionDict e = Exception e => ExceptionDict

  data ExitCase a
    = ExitCaseSuccess a
    | ExitCaseException SomeException
    | ExitCaseAbort

  generalBracket ::
    IO a -> (a -> ExitCase b -> IO c) -> (a -> IO b) -> IO (b, c)
  generalBracket acquire release use = mask $ \ unmasked -> do
    resource <- acquire
    b <- unmasked (use resource) `catch` \ e -> do
      _ <- release resource (ExitCaseException e)
      throwIO e
    c <- release resource (ExitCaseSuccess b)
    return (b, c)
#-}

{-# COMPILE GHC Exception = type ExceptionDict #-}
{-# COMPILE GHC SomeException = type SomeException #-}
{-# COMPILE GHC IOException = type IOException #-}
{-# COMPILE GHC Exception-SomeException = ExceptionDict #-}
{-# COMPILE GHC Exception-IOException = ExceptionDict #-}
{-# COMPILE GHC toException = \ _ ExceptionDict -> toException #-}
{-# COMPILE GHC fromException = \ _ ExceptionDict -> fromException #-}
{-# COMPILE GHC displayException = \ _ ExceptionDict -> pack . displayException #-}
{-# COMPILE GHC ExitCase = data ExitCase (ExitCaseSuccess | ExitCaseException | ExitCaseAbort) #-}
{-# COMPILE GHC throwIO = \ _ _ ExceptionDict -> throwIO #-}
{-# COMPILE GHC catchIO = \ _ _ ExceptionDict -> catch #-}
{-# COMPILE GHC generalBracketIO = \ _ _ _ -> generalBracket #-}
