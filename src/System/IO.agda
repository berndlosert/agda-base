module System.IO where

open import Prelude

open import Data.Int

private variable r : Set

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStrLn (f s)

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
