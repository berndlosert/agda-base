{-# OPTIONS --type-in-type #-}

module Data.String.Encoding where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.ByteString

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

postulate
  encodeUtf8 : String -> ByteString

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Data.Text.Encoding #-}
{-# COMPILE GHC encodeUtf8 = encodeUtf8 #-}
