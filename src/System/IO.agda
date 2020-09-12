{-# OPTIONS --type-in-type #-}

module System.IO where

open import Prelude

open import Control.Monad.IO.Class
open import Control.Monad.IO.Unlift
open import Data.Int

open Control.Monad.IO.Class public using (MonadIO-IO)
open Control.Monad.IO.Unlift public using (MonadUnliftIO-IO)

private
  variable
    a b r : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- Base module
-------------------------------------------------------------------------------

module Base where

  -- Console IO

  postulate
    putStr : String -> IO Unit
    putStrLn : String -> IO Unit
    getLine : IO String
    getContents : IO String

  interact : (String -> String) -> IO Unit
  interact f = do
    s <- getContents
    putStrLn (f s)

  print : {{_ : Show a}} -> a -> IO Unit
  print x = putStrLn (show x)

  -- File IO

  FilePath : Set
  FilePath = String

  data IOMode : Set where
    ReadMode WriteMode AppendMode ReadWriteMode : IOMode

  data BufferMode : Set where
    NoBuffering : BufferMode
    LineBuffering : BufferMode
    BlockBuffering : Maybe Int64 -> BufferMode

  postulate
    Handle : Set
    stdin stdout stderr : Handle
    withFile : FilePath -> IOMode -> (Handle -> IO r) -> IO r
    openFile : FilePath -> IOMode -> IO Handle
    hClose : Handle -> IO Unit
    readFile : FilePath -> IO String
    writeFile : FilePath -> String -> IO Unit
    appendFile : FilePath -> String -> IO Unit
    hFileSize : Handle -> IO Nat
    hSetFileSize : Handle -> Nat -> IO Unit
    hIsEOF : Handle -> IO Bool
    isEOF : IO Bool
    hSetBuffering : Handle -> BufferMode -> IO Unit
    hGetBuffering : Handle -> IO BufferMode
    hFlush : Handle -> IO Unit

  {-# FOREIGN GHC import System.IO (Handle, IOMode (..), BufferMode (..)) #-}
  {-# FOREIGN GHC import Data.Text (unpack) #-}
  {-# FOREIGN GHC import qualified System.IO as IO #-}
  {-# FOREIGN GHC import qualified Data.Text.IO as T #-}
  {-# COMPILE GHC putStr = T.putStr #-}
  {-# COMPILE GHC putStrLn = T.putStrLn #-}
  {-# COMPILE GHC getLine = T.getLine #-}
  {-# COMPILE GHC getContents = T.getContents #-}
  {-# COMPILE GHC IOMode = data IOMode (ReadMode | WriteMode | AppendMode | ReadWriteMode) #-}
  {-# COMPILE GHC BufferMode = data BufferMode (NoBuffering | LineBuffering | BlockBuffering) #-}
  {-# COMPILE GHC Handle = type Handle #-}
  {-# COMPILE GHC stdin = IO.stdin #-}
  {-# COMPILE GHC stdout = IO.stdout #-}
  {-# COMPILE GHC stderr = IO.stderr #-}
  {-# COMPILE GHC withFile = \ _ -> IO.withFile . unpack #-}
  {-# COMPILE GHC openFile = IO.openFile . unpack  #-}
  {-# COMPILE GHC hClose = IO.hClose #-}
  {-# COMPILE GHC readFile = T.readFile . unpack #-}
  {-# COMPILE GHC writeFile = T.writeFile . unpack #-}
  {-# COMPILE GHC appendFile = T.appendFile . unpack #-}
  {-# COMPILE GHC hFileSize = IO.hFileSize #-}
  {-# COMPILE GHC hSetFileSize = IO.hSetFileSize #-}
  {-# COMPILE GHC hIsEOF = IO.hIsEOF #-}
  {-# COMPILE GHC isEOF = IO.isEOF #-}
  {-# COMPILE GHC hSetBuffering = IO.hSetBuffering #-}
  {-# COMPILE GHC hGetBuffering = IO.hGetBuffering #-}
  {-# COMPILE GHC hFlush = IO.hFlush #-}

open Base public
  using (
    FilePath;
    IOMode; ReadMode; WriteMode; AppendMode; ReadWriteMode;
    BufferMode; NoBuffering; LineBuffering; BlockBuffering;
    Handle; stdin; stdout; stderr
  )

-------------------------------------------------------------------------------
-- Console IO (lifted)
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

print : {{_ : Show a}} {{_ : MonadIO m}} -> a -> m Unit
print = liftIO <<< Base.print

-------------------------------------------------------------------------------
-- File IO (lifted)
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
