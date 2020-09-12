{-# OPTIONS --type-in-type #-}

module Data.ByteString where

postulate
  ByteString : Set

{-# FOREIGN GHC import qualified Data.ByteString as ByteString #-}
{-# FOREIGN GHC import Data.ByteString (ByteString) #-}
{-# COMPILE GHC ByteString = type ByteString #-}
