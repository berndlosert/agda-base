{-# OPTIONS --type-in-type #-}

module Data.ByteString where

-------------------------------------------------------------------------------
-- ByteString
-------------------------------------------------------------------------------

postulate
  ByteString : Set

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Data.ByteString as ByteString #-}
{-# FOREIGN GHC import Data.ByteString (ByteString) #-}
{-# COMPILE GHC ByteString = type ByteString #-}
