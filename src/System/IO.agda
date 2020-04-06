{-# OPTIONS --type-in-type #-}

module System.IO where

open import Agda.Builtin.IO public using (IO)
open import Control.Applicative using (Applicative)
open import Control.Applicative public using (_<*>_; pure)
open import Control.Monad using (Monad)
open import Control.Monad public using (_>>=_; return)
open import Data.Function using (_<<<_; _>>>_)
open import Data.Functor using (Functor)
open import Data.Functor public using (map)
open import Data.Monoid using (Monoid; mempty)
open import Data.Semigroup using (Semigroup; _<>_)
open import Data.String using (String)
open import Data.String.Show using (Show; show)
open import Data.Unit using (Unit)
open import Data.Void using (Void)

private variable A B : Set

postulate
  mapIO : (A -> B) -> IO A -> IO B
  pureIO : A -> IO A
  apIO : IO (A -> B) -> IO A -> IO B
  bindIO : IO A -> (A -> IO B) -> IO B
  putStr : String -> IO Unit
  putStrLn : String -> IO Unit
  getLine : IO String
  getContents : IO String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC pureIO = \ _ a -> pure a #-}
{-# COMPILE GHC bindIO = \ _ _ ma f -> ma >>= f #-}
{-# COMPILE GHC putStr = Text.putStr #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC getContents = Text.getContents #-}

instance
  functorIO : Functor IO
  functorIO .map f io = bindIO io (f >>> pureIO)

  applicativeIO : Applicative IO
  applicativeIO .pure = pureIO
  applicativeIO ._<*>_ fs xs =
    bindIO fs (\ f -> bindIO xs (\ x -> pureIO (f x)))

  monadIO : Monad IO
  monadIO ._>>=_ = bindIO

  semigroupIO : {{_ : Semigroup A}} -> Semigroup (IO A)
  semigroupIO ._<>_ x y = (| _<>_ x y |)

  monoidIO : {{_ : Monoid A}} -> Monoid (IO A)
  monoidIO .mempty = return mempty

print : {{_ : Show A}} -> A -> IO Unit
print x = putStrLn (show x)

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStr (f s)
