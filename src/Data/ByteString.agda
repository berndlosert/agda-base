{-# OPTIONS --type-in-type #-}

module Data.ByteString where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (putStrLn)

open import Data.Word

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- ByteString
-------------------------------------------------------------------------------

postulate
  ByteString : Set
  putStrLn : ByteString -> IO Unit

private
  postulate
    primPack : List Word8 -> ByteString
    primUnpack : ByteString -> List Word8
    primAppend : ByteString -> ByteString -> ByteString
    primEmpty : ByteString
    primSingleton : Word8 -> ByteString
    primFoldr : (Word8 -> a -> a) -> a -> ByteString -> a

instance
  Packed-ByteString-Word8 : Packed ByteString Word8
  Packed-ByteString-Word8 .pack = primPack
  Packed-ByteString-Word8 .unpack = primUnpack

  Semigroup-ByteString : Semigroup ByteString
  Semigroup-ByteString ._<>_ = primAppend

  Monoid-ByteString : Monoid ByteString
  Monoid-ByteString .neutral = primEmpty

  IsBuildable-ByteString-Word8 : IsBuildable ByteString Word8
  IsBuildable-ByteString-Word8 .singleton = primSingleton

  IsFoldable-ByteString-Word8 : IsFoldable ByteString Word8
  IsFoldable-ByteString-Word8 .foldMap f bs =
    primFoldr (\ w accum -> f w <> accum) neutral bs

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Data.ByteString as ByteString #-}
{-# FOREIGN GHC import qualified Data.ByteString.Char8 as Char8 #-}
{-# FOREIGN GHC import Data.ByteString (ByteString) #-}
{-# COMPILE GHC ByteString = type ByteString #-}
{-# COMPILE GHC primPack = ByteString.pack #-}
{-# COMPILE GHC primUnpack = ByteString.unpack #-}
{-# COMPILE GHC primAppend = ByteString.append #-}
{-# COMPILE GHC primEmpty = ByteString.empty #-}
{-# COMPILE GHC primSingleton = ByteString.singleton #-}
{-# COMPILE GHC primFoldr = ByteString.foldr #-}
{-# COMPILE GHC putStrLn = Char8.putStrLn #-}
