module System.IO where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Int64

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b r : Set

-------------------------------------------------------------------------------
-- Console IO
-------------------------------------------------------------------------------

postulate
  putStr : String -> IO Unit
  putStrLn : String -> IO Unit
  getLine : IO String
  getContents : IO String

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStrLn (f s)

print : {{Show a}} -> a -> IO Unit
print x = putStrLn (show x)

{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC putStr = T.putStr #-}
{-# COMPILE GHC putStrLn = T.putStrLn #-}
{-# COMPILE GHC getLine = T.getLine #-}
{-# COMPILE GHC getContents = T.getContents #-}

-------------------------------------------------------------------------------
-- File IO
-------------------------------------------------------------------------------

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

  TextEncoding : Set
  latin1 : TextEncoding
  utf8 utf8-bom : TextEncoding
  utf16 utf16le utf16be : TextEncoding
  utf32 utf32le utf32be : TextEncoding
  localeEncoding : TextEncoding
  char8 : TextEncoding

  hSetEncoding : Handle -> TextEncoding -> IO Unit
  hGetEncoding : Handle -> IO (Maybe TextEncoding)

  withFile : FilePath -> IOMode -> (Handle -> IO r) -> IO r
  openFile : FilePath -> IOMode -> IO Handle

  hGetContents : Handle -> IO String
  hGetLine : Handle -> IO String

  hClose : Handle -> IO Unit

  hFileSize : Handle -> IO Nat
  hSetFileSize : Handle -> Nat -> IO Unit

  hIsEOF : Handle -> IO Bool
  isEOF : IO Bool

  hSetBuffering : Handle -> BufferMode -> IO Unit
  hGetBuffering : Handle -> IO BufferMode

  hFlush : Handle -> IO Unit

  hPutChar : Handle -> Char -> IO Unit
  hPutStr : Handle -> String -> IO Unit
  hPutStrLn : Handle -> String -> IO Unit

private
  postulate
    hEq : Handle -> Handle -> Bool
    hShow : Handle -> String

readFile : TextEncoding -> FilePath -> IO String
readFile enc fp = withFile fp ReadMode \ h -> do
  hSetEncoding h enc
  hGetContents h

writeFile : TextEncoding -> FilePath -> String -> IO Unit
writeFile enc fp str = withFile fp WriteMode \ h -> do
  hSetEncoding h utf8
  hPutStr h str

appendFile : TextEncoding -> FilePath -> String -> IO Unit
appendFile enc fp str = withFile fp AppendMode \ h -> do
  hSetEncoding h utf8
  hPutStr h str

instance
  Eq-Handle : Eq Handle
  Eq-Handle ._==_ = hEq

  Show-Handle : Show Handle
  Show-Handle .showsPrec _ h = showString $ hShow h

-------------------------------------------------------------------------------
-- File IO FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import System.IO (IOMode (..), BufferMode (..)) #-}
{-# FOREIGN GHC import Data.Text (unpack, pack) #-}
{-# FOREIGN GHC import qualified System.IO as IO #-}
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC IOMode = data IOMode (ReadMode | WriteMode | AppendMode | ReadWriteMode) #-}
{-# COMPILE GHC BufferMode = data BufferMode (NoBuffering | LineBuffering | BlockBuffering) #-}
{-# COMPILE GHC Handle = type IO.Handle #-}
{-# COMPILE GHC stdin = IO.stdin #-}
{-# COMPILE GHC stdout = IO.stdout #-}
{-# COMPILE GHC stderr = IO.stderr #-}
{-# COMPILE GHC TextEncoding = type IO.TextEncoding #-}
{-# COMPILE GHC latin1 = IO.latin1 #-}
{-# COMPILE GHC utf8 = IO.utf8 #-}
{-# COMPILE GHC utf8-bom = IO.utf8_bom #-}
{-# COMPILE GHC utf16 = IO.utf16 #-}
{-# COMPILE GHC utf16le = IO.utf16le #-}
{-# COMPILE GHC utf16be = IO.utf16be #-}
{-# COMPILE GHC utf32 = IO.utf32 #-}
{-# COMPILE GHC utf32le = IO.utf32le #-}
{-# COMPILE GHC utf32be = IO.utf32be #-}
{-# COMPILE GHC localeEncoding = IO.localeEncoding #-}
{-# COMPILE GHC char8 = IO.char8 #-}
{-# COMPILE GHC hSetEncoding = IO.hSetEncoding #-}
{-# COMPILE GHC hGetEncoding = IO.hGetEncoding #-}
{-# COMPILE GHC withFile = \ _ -> IO.withFile . unpack #-}
{-# COMPILE GHC openFile = IO.openFile . unpack  #-}
{-# COMPILE GHC hGetContents = T.hGetContents #-}
{-# COMPILE GHC hGetLine = T.hGetLine #-}
{-# COMPILE GHC hClose = IO.hClose #-}
{-# COMPILE GHC hFileSize = IO.hFileSize #-}
{-# COMPILE GHC hSetFileSize = IO.hSetFileSize #-}
{-# COMPILE GHC hIsEOF = IO.hIsEOF #-}
{-# COMPILE GHC isEOF = IO.isEOF #-}
{-# COMPILE GHC hSetBuffering = IO.hSetBuffering #-}
{-# COMPILE GHC hGetBuffering = IO.hGetBuffering #-}
{-# COMPILE GHC hFlush = IO.hFlush #-}
{-# COMPILE GHC hPutChar = IO.hPutChar #-}
{-# COMPILE GHC hPutStr = \ h s -> IO.hPutStr h (unpack s) #-}
{-# COMPILE GHC hPutStrLn = \ h s -> IO.hPutStrLn h (unpack s) #-}
{-# COMPILE GHC hEq = (==) #-}
{-# COMPILE GHC hShow = pack . show #-}
