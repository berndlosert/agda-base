module Data.String.Encoding where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Data.Bifunctor
open import Data.Bytes
open import Data.Show
open import Data.String as String using ()
open import Data.Word
open import Prelude

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

postulate
  encodeUtf8 : String -> Bytes
  decodeUtf8 : Bytes -> String

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Data.Text.Encoding #-}
{-# COMPILE GHC encodeUtf8 = encodeUtf8 #-}
{-# COMPILE GHC decodeUtf8 = decodeUtf8Lenient #-}
