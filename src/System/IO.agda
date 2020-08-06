module System.IO where

open import Prelude

open import Data.Int

private variable a b r : Set

-------------------------------------------------------------------------------
-- IO
-------------------------------------------------------------------------------

postulate IO : Set -> Set

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

private
  postulate
    mapIO : (a -> b) -> IO a -> IO b
    pureIO : a -> IO a
    apIO : IO (a -> b) -> IO a -> IO b
    bindIO : IO a -> (a -> IO b) -> IO b

instance
  semigroupIO : {{_ : Semigroup a}} -> Semigroup (IO a)
  semigroupIO ._<>_ x y = let _<*>_ = apIO; pure = pureIO in
    (| _<>_ x y |)

  monoidIO : {{_ : Monoid a}} -> Monoid (IO a)
  monoidIO .neutral = pureIO neutral

  functorIO : Functor IO
  functorIO .map = mapIO

  applicativeIO : Applicative IO
  applicativeIO .pure = pureIO
  applicativeIO ._<*>_ = apIO

  monadIO : Monad IO
  monadIO ._>>=_ = bindIO

-------------------------------------------------------------------------------
-- Console IO stuff
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

print : {{_ : Show a}} -> a -> IO Unit
print x = putStrLn (show x)

-------------------------------------------------------------------------------
-- File IO stuff
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
{-# COMPILE GHC mapIO = \ _ _ -> fmap #-}
{-# COMPILE GHC pureIO = \ _ -> pure #-}
{-# COMPILE GHC apIO = \ _ _ -> (<*>) #-}
{-# COMPILE GHC bindIO = \ _ _ -> (>>=) #-}
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
