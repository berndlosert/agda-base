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
    a b c e : Set

-------------------------------------------------------------------------------
-- Exception, SomeException, IOException
-------------------------------------------------------------------------------

postulate
  Exception : Set -> Set
  SomeException : Set
  IOException : Set

  toException : {{Exception e}} -> e -> SomeException
  fromException : {{Exception e}} -> SomeException -> Maybe e
  displayException : {{Exception e}} -> e -> String

-------------------------------------------------------------------------------
-- MonadThrow
-------------------------------------------------------------------------------

record MonadThrow (e : Set) (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    throw : e -> m a

open MonadThrow {{...}} public

-------------------------------------------------------------------------------
-- MonadCatch
-------------------------------------------------------------------------------

record MonadCatch (e : Set) (m : Set -> Set) : Set where
  field
    overlap {{MonadThrow-super}} : MonadThrow e m
    catch : m a -> (e -> m a) -> m a

  catchJust : (e -> Maybe b) -> m a -> (b -> m a) -> m a
  catchJust p ma handler = catch ma \ e -> maybe (throw e) handler (p e)

  handle : (e -> m a) -> m a -> m a
  handle = flip catch

  handleJust : (e -> Maybe b) -> (b -> m a) -> m a -> m a
  handleJust = flip <<< catchJust

  try : m a -> m (Either e a)
  try ma = catch (map right ma) (pure <<< left)

  tryJust : (e -> Maybe b) -> m a -> m (Either b a)
  tryJust p ma = try ma >>= \ where
    (right v) -> pure (right v)
    (left e) -> maybe (throw e) (pure <<< left) (p e)

open MonadCatch {{...}} public

-------------------------------------------------------------------------------
-- MonadBracket
-------------------------------------------------------------------------------

data ExitCase (e a : Set) : Set where
  exitCaseSuccess : a -> ExitCase e a
  exitCaseException : e -> ExitCase e a
  exitCaseAbort : ExitCase e a

record MonadBracket (e : Set) (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    generalBracket : m a
      -> (a -> ExitCase e b -> m c)
      -> (a -> m b)
      -> m (Pair b c)

  bracket : m a -> (a -> m c) -> (a -> m b) -> m b
  bracket acquire release =
    map fst <<< generalBracket acquire (\ a _ -> release a)

  bracket' : m a -> m c -> m b -> m b
  bracket' before after action = bracket before (const after) (const action)

  bracketOnError : m a -> (a -> m c) -> (a -> m b) -> m b
  bracketOnError acquire release =
    map fst <<< generalBracket acquire \ where
      _ (exitCaseSuccess _) -> pure tt
      a _ -> do
        release a
        pure tt

  onError : m a -> m b -> m a
  onError action handler =
    bracketOnError (pure tt) (const handler) (const action)

  finally : m a -> m b -> m a
  finally action finalizer = bracket' (pure tt) finalizer action

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
    generalBracketIO : IO a -> (a -> ExitCase SomeException b -> IO c)
      -> (a -> IO b) -> IO (Pair b c)

instance
  MonadThrow-Either : MonadThrow e (Either e)
  MonadThrow-Either .throw = left

  MonadThrow-IO : {{Exception e}} -> MonadThrow e IO
  MonadThrow-IO .throw = throwIO

  MonadCatch-Either : MonadCatch e (Either e)
  MonadCatch-Either .catch (left e) f = f e
  MonadCatch-Either .catch x _ = x

  MonadCatch-IO : {{Exception e}} -> MonadCatch e IO
  MonadCatch-IO .catch = catchIO

  MonadBracket-Either : MonadBracket e (Either e)
  MonadBracket-Either .generalBracket acquire release use =
    case acquire of \ where
      (left e) -> left e
      (right resource) ->
        case use resource of \ where
          (left e) -> release resource (exitCaseException e) >> left e
          (right b) -> do
            c <- release resource (exitCaseSuccess b)
            pure (b , c)

  MonadBracket-IO : MonadBracket SomeException IO
  MonadBracket-IO .generalBracket = generalBracketIO

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC
  import Control.Exception
  import Data.Text (pack)

  data ExceptionDict e = Exception e => ExceptionDict

  data ExitCase e a
    = ExitCaseSuccess a
    | ExitCaseException e
    | ExitCaseAbort

  generalBracket ::
    IO a -> (a -> ExitCase SomeException b -> IO c) -> (a -> IO b) -> IO (b, c)
  generalBracket acquire release use = mask $ \ unmasked -> do
    resource <- acquire
    b <- unmasked (use resource) `catch` \ e -> do
      _ <- release resource (ExitCaseException e)
      throwIO e
    c <- release resource (ExitCaseSuccess b)
    pure (b, c)
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
