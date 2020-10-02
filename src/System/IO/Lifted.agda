module System.IO.Lifted where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude
  hiding (putStr; putStrLn; getLine; getContents; interact; print)

open import Control.Monad.IO.Class
open import Control.Monad.IO.Unlift
open import System.IO as Base using ()

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.IO.Class public
  using (MonadIO-IO)

open Control.Monad.IO.Unlift public
  using (MonadUnliftIO-IO)

open Base public
  using (
    FilePath;
    IOMode; ReadMode; WriteMode; AppendMode; ReadWriteMode;
    BufferMode; NoBuffering; LineBuffering; BlockBuffering;
    Handle; stdin; stdout; stderr
  )

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b r : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- Console IO
-------------------------------------------------------------------------------

module _ {{_ : MonadIO m}} where

  putStr : String -> m Unit
  putStr = liftIO <<< Prelude.putStr

  putStrLn : String -> m Unit
  putStrLn = liftIO <<< Prelude.putStrLn

  getLine : m String
  getLine = liftIO (Prelude.getLine)

  getContents : m String
  getContents = liftIO (Prelude.getContents)

  interact : (String -> String) -> m Unit
  interact = liftIO <<< Prelude.interact

print : {{_ : Show a}} {{_ : MonadIO m}} -> a -> m Unit
print = liftIO <<< Prelude.print

-------------------------------------------------------------------------------
-- File IO
-------------------------------------------------------------------------------

withFile : {{_ : MonadUnliftIO m}}
  -> FilePath -> IOMode -> (Handle -> m r) -> m r
withFile path mode handler = withRunInIO \ run ->
  Base.withFile path mode (run <<< handler)

module _ {{_ : MonadIO m}} where

  openFile : FilePath -> IOMode -> m Handle
  openFile path mode = liftIO (Base.openFile path mode)

  hClose : Handle -> m Unit
  hClose = liftIO <<< Base.hClose

  readFile : FilePath -> m String
  readFile = liftIO <<< Base.readFile

  writeFile : FilePath -> String -> m Unit
  writeFile path = liftIO <<< Base.writeFile path

  appendFile : FilePath -> String -> m Unit
  appendFile path = liftIO <<< Base.appendFile path

  hFileSize : Handle -> m Nat
  hFileSize = liftIO <<< Base.hFileSize

  hSetFileSize : Handle -> Nat -> m Unit
  hSetFileSize handle = liftIO <<< Base.hSetFileSize handle

  hIsEOF : Handle -> m Bool
  hIsEOF = liftIO <<< Base.hIsEOF

  isEOF : m Bool
  isEOF = liftIO (Base.isEOF)

  hSetBuffering : Handle -> BufferMode -> m Unit
  hSetBuffering handle = liftIO <<< Base.hSetBuffering handle

  hGetBuffering : Handle -> m BufferMode
  hGetBuffering = liftIO <<< Base.hGetBuffering

  hFlush : Handle -> m Unit
  hFlush = liftIO <<< Base.hFlush
