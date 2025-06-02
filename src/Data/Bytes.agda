module Data.Bytes where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Show
open import Data.Word

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Bytes
-------------------------------------------------------------------------------

postulate
  Bytes : Type
  pack : List Word8 -> Bytes
  unpack : Bytes -> List Word8
  packChars : List Char -> Bytes
  unpackChars : Bytes -> List Char
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

  Show-Bytes : Show Bytes
  Show-Bytes .show = showDefault
  Show-Bytes .showsPrec prec bs = showsPrec prec (unpackChars bs)

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# FOREIGN GHC import qualified Data.ByteString.Char8 as C #-}
{-# FOREIGN GHC import Data.ByteString (ByteString) #-}
{-# COMPILE GHC Bytes = type ByteString #-}
{-# COMPILE GHC pack = BS.pack #-}
{-# COMPILE GHC unpack = BS.unpack #-}
{-# COMPILE GHC packChars = C.pack #-}
{-# COMPILE GHC unpackChars = C.unpack #-}
{-# COMPILE GHC append = BS.append #-}
{-# COMPILE GHC empty = BS.empty #-}
{-# COMPILE GHC singleton = BS.singleton #-}
{-# COMPILE GHC foldr = \ _ -> BS.foldr #-}
{-# COMPILE GHC null = BS.null #-}
