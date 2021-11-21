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
-- Exception, SomeException
-------------------------------------------------------------------------------

postulate
  Exception : Set -> Set
  SomeException : Set

  toException : {{Exception e}} -> e -> SomeException
  fromException : {{Exception e}} -> SomeException -> Maybe e
  displayException : {{Exception e}} -> e -> String

  instance
    Exception-SomeException : Exception SomeException

-------------------------------------------------------------------------------
-- MonadThrow
-------------------------------------------------------------------------------

record MonadThrow (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    throw : {{Exception e}} -> e -> m a

open MonadThrow {{...}} public

-------------------------------------------------------------------------------
-- MonadCatch
-------------------------------------------------------------------------------

record MonadCatch (m : Set -> Set) : Set where
  infixl 9 _catch_
  field
    overlap {{MonadThrow-super}} : MonadThrow m
    _catch_ : {{Exception e}} -> m a -> (e -> m a) -> m a

  infixl 9 _catchAll_
  _catchAll_ : m a -> (SomeException -> m a) -> m a
  _catchAll_ = _catch_

  catchIf : {{Exception e}} -> (e -> Bool) -> m a -> (e -> m a) -> m a
  catchIf p action handler =
    action catch \ e -> if p e then handler e else throw e

  catchJust : {{Exception e}} -> (e -> Maybe b) -> m a -> (b -> m a) -> m a
  catchJust p action handler =
    action catch \ e -> maybe (throw e) handler (p e)

  handle : {{Exception e}} -> (e -> m a) -> m a -> m a
  handle = flip _catch_

  handleJust : {{Exception e}} -> (e -> Maybe b) -> (b -> m a) -> m a -> m a
  handleJust = flip <<< catchJust

  try : {{Exception e}} -> m a -> m (Either e a)
  try action = (map right action) catch (pure <<< left)

  tryJust : {{Exception e}} -> (e -> Maybe b) -> m a -> m (Either b a)
  tryJust p action = do
    res <- try action
    case res of \ where
      (right v) -> pure (right v)
      (left e) -> maybe (throw e) (pure <<< left) (p e)

  infixl 9 _onException_
  _onException_ : m a -> m b -> m a
  action onException handler = action catchAll \ e -> handler *> throw e

open MonadCatch {{...}} public

-------------------------------------------------------------------------------
-- MonadBracket
-------------------------------------------------------------------------------

data ExitCase (a : Set) : Set where
  exitCaseSuccess : a -> ExitCase a
  exitCaseException : SomeException -> ExitCase a
  exitCaseAbort : ExitCase a

record MonadBracket (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    generalBracket : m a
      -> (a -> ExitCase b -> m c)
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

  infixl 9 _onError_
  _onError_ : m a -> m b -> m a
  action onError handler =
    bracketOnError (pure tt) (const handler) (const action)

  infixl 9 _finally_
  _finally_ : m a -> m b -> m a
  action finally finalizer = bracket' (pure tt) finalizer action

open MonadBracket {{...}} public

-------------------------------------------------------------------------------
-- IOException
-------------------------------------------------------------------------------

postulate
  IOException : Set
  userException : String -> IOException

  instance
    Exception-IOException : Exception IOException

-------------------------------------------------------------------------------
-- IO instances
-------------------------------------------------------------------------------

private
  postulate
    throwIO : {{Exception e}} -> e -> IO a
    catchIO : {{Exception e}} -> IO a -> (e -> IO a) -> IO a
    generalBracketIO : IO a -> (a -> ExitCase b -> IO c)
      -> (a -> IO b) -> IO (Pair b c)

instance
  MonadThrow-IO : MonadThrow IO
  MonadThrow-IO .throw = throwIO

  MonadCatch-IO : MonadCatch IO
  MonadCatch-IO ._catch_ = catchIO

  MonadBracket-IO : MonadBracket IO
  MonadBracket-IO .generalBracket = generalBracketIO

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC
  import Control.Exception
  import Data.Text (pack, unpack)

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
{-# COMPILE GHC userException = userError . unpack #-}
