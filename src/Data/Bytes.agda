{-# OPTIONS --type-in-type #-}

module Data.Bytes where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (pack; unpack)

open import Data.Word

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Bytes
-------------------------------------------------------------------------------

postulate
  Bytes : Set
  putStrLn : Bytes -> IO Unit
  pack : List Word8 -> Bytes
  unpack : Bytes -> List Word8
  append : Bytes -> Bytes -> Bytes
  empty : Bytes
  singleton : Word8 -> Bytes
  foldr : (Word8 -> a -> a) -> a -> Bytes -> a
  null : Bytes -> Bool

instance
  Semigroup-Bytes : Semigroup Bytes
  Semigroup-Bytes ._<>_ = append

  Monoid-Bytes : Monoid Bytes
  Monoid-Bytes .mempty = empty

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# FOREIGN GHC import qualified Data.ByteString.Char8 as Char8 #-}
{-# FOREIGN GHC import Data.ByteString (ByteString) #-}
{-# COMPILE GHC Bytes = type ByteString #-}
{-# COMPILE GHC pack = BS.pack #-}
{-# COMPILE GHC unpack = BS.unpack #-}
{-# COMPILE GHC append = BS.append #-}
{-# COMPILE GHC empty = BS.empty #-}
{-# COMPILE GHC singleton = BS.singleton #-}
{-# COMPILE GHC foldr = \ _ -> BS.foldr #-}
{-# COMPILE GHC null = BS.null #-}
{-# COMPILE GHC putStrLn = Char8.putStrLn #-}
