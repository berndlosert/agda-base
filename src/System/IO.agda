{-# OPTIONS --type-in-type #-}

module System.IO where

open import Prelude

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
  BlockBuffering : Maybe Nat -> BufferMode

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

{-# FOREIGN GHC

  import System.IO (Handle, IOMode (..), BufferMode (..))
  import Data.Text (unpack)
  import qualified System.IO as IO
  import qualified Data.Text.IO as T

  data BufferMode'
    = NoBuffering'
    | LineBuffering'
    | BlockBuffering' (Maybe Integer)

  fromBufferMode' NoBuffering' = NoBuffering
  fromBufferMode' LineBuffering' = LineBuffering
  fromBufferMode' (BlockBuffering' m) = BlockBuffering (fmap fromInteger m)

  toBufferMode' NoBuffering = NoBuffering'
  toBufferMode' LineBuffering = LineBuffering'
  toBufferMode' (BlockBuffering m) = BlockBuffering' (fmap toInteger m)

  hSetBuffering' :: Handle -> BufferMode' -> IO ()
  hSetBuffering' hdl mode = IO.hSetBuffering hdl (fromBufferMode' mode)

  hGetBuffering' :: Handle -> IO BufferMode'
  hGetBuffering' hdl = fmap toBufferMode' (IO.hGetBuffering hdl)
#-}

{-# COMPILE GHC IOMode = data IOMode (ReadMode | WriteMode | AppendMode | ReadWriteMode) #-}
{-# COMPILE GHC BufferMode = data BufferMode' (NoBuffering' | LineBuffering' | BlockBuffering') #-}
{-# COMPILE GHC Handle = type Handle #-}
{-# COMPILE GHC stdin = IO.stdin #-}
{-# COMPILE GHC stdout = IO.stdout #-}
{-# COMPILE GHC stderr = IO.stderr #-}
{-# COMPILE GHC withFile = \ _ fp mode hdl -> IO.withFile (unpack fp) mode hdl #-}
{-# COMPILE GHC openFile = \ fp mode -> IO.openFile (unpack fp) mode  #-}
{-# COMPILE GHC hClose = IO.hClose #-}
{-# COMPILE GHC readFile = \ fp -> T.readFile (unpack fp) #-}
{-# COMPILE GHC writeFile = \ fp str -> T.writeFile (unpack fp) str #-}
{-# COMPILE GHC appendFile = \ fp str -> T.appendFile (unpack fp) str #-}
{-# COMPILE GHC hFileSize = IO.hFileSize #-}
{-# COMPILE GHC hSetFileSize = IO.hSetFileSize #-}
{-# COMPILE GHC hIsEOF = IO.hIsEOF #-}
{-# COMPILE GHC isEOF = IO.isEOF #-}
{-# COMPILE GHC hSetBuffering = hSetBuffering' #-}
{-# COMPILE GHC hGetBuffering = hGetBuffering' #-}
{-# COMPILE GHC hFlush = IO.hFlush #-}
