module System.IO.Lifted where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.IO.Class
open import Control.Monad.IO.Unlift
open import System.IO as Base using ()
open import String.Show

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
    Handle; stdin; stdout; stderr;
    TextEncoding; latin1; utf8; utf8-bom; utf16; utf16le; utf16be;
    utf32; utf32le; utf32be; localeEncoding; char8
  )

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b r : Type
    m : Type -> Type

-------------------------------------------------------------------------------
-- Console IO
-------------------------------------------------------------------------------

module _ {{_ : MonadIO m}} where

  putStr : String -> m Unit
  putStr = liftIO <<< Base.putStr

  putStrLn : String -> m Unit
  putStrLn = liftIO <<< Base.putStrLn

  getLine : m String
  getLine = liftIO (Base.getLine)

  getContents : m String
  getContents = liftIO (Base.getContents)

  interact : (String -> String) -> m Unit
  interact = liftIO <<< Base.interact

print : {{Show a}} -> {{MonadIO m}} -> a -> m Unit
print = liftIO <<< Base.print

-------------------------------------------------------------------------------
-- File IO
-------------------------------------------------------------------------------

withFile : {{MonadUnliftIO m}}
  -> FilePath -> IOMode -> (Handle -> m r) -> m r
withFile path mode handler = withRunInIO \ run ->
  Base.withFile path mode (run <<< handler)

module _ {{_ : MonadIO m}} where

  hSetEncoding : Handle -> TextEncoding -> m Unit
  hSetEncoding h = liftIO <<< Base.hSetEncoding h

  hGetEncoding : Handle -> m (Maybe TextEncoding)
  hGetEncoding = liftIO <<< Base.hGetEncoding

  openFile : FilePath -> IOMode -> m Handle
  openFile path mode = liftIO (Base.openFile path mode)

  hGetContents : Handle -> m String
  hGetContents = liftIO <<< Base.hGetContents

  hGetLine : Handle -> m String
  hGetLine = liftIO <<< Base.hGetLine

  hClose : Handle -> m Unit
  hClose = liftIO <<< Base.hClose

  readFile : TextEncoding -> FilePath -> m String
  readFile enc = liftIO <<< Base.readFile enc

  writeFile : TextEncoding -> FilePath -> String -> m Unit
  writeFile enc path = liftIO <<< Base.writeFile enc path

  appendFile : TextEncoding -> FilePath -> String -> m Unit
  appendFile enc path = liftIO <<< Base.appendFile enc path

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
