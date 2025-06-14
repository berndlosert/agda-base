module Data.String.Encoding where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Bifunctor
open import Data.Bytes
open import Data.String as String using ()
open import Data.String.Show
open import Data.Word

-------------------------------------------------------------------------------
-- Error handling types
-------------------------------------------------------------------------------

private
  data UnicodeException : Type where
    decodeError : List Char -> Maybe Word8 -> UnicodeException
    encodeError : List Char -> Maybe Char -> UnicodeException

record DecodeError : Type where
  field
    errorMessage : String
    invalidInput : Maybe Word8

private
  unsafeUnicodeExceptionToDecodeError : UnicodeException -> DecodeError
  unsafeUnicodeExceptionToDecodeError (decodeError cs mw8) =
    record { errorMessage = String.pack cs; invalidInput = mw8 }
  unsafeUnicodeExceptionToDecodeError (encodeError _ _) = undefined

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

postulate
  encodeUtf8 : String -> Bytes

private
  postulate
    decodeUtf8' : Bytes -> Either UnicodeException String

decodeUtf8 : Bytes -> Either DecodeError String
decodeUtf8 bs = lmap unsafeUnicodeExceptionToDecodeError (decodeUtf8' bs)

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Data.Text.Encoding #-}
{-# FOREIGN GHC import Data.Text.Encoding.Error #-}
{-# COMPILE GHC UnicodeException = data UnicodeException (DecodeError | EncodeError) #-}
{-# COMPILE GHC encodeUtf8 = encodeUtf8 #-}
{-# COMPILE GHC decodeUtf8' = decodeUtf8' #-}
