{-# OPTIONS --type-in-type #-}

module Data.ByteString where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (null; putStrLn)

-------------------------------------------------------------------------------
-- ByteString
-------------------------------------------------------------------------------

postulate
  ByteString : Set
  null : ByteString -> Bool
  putStrLn : ByteString -> IO Unit
  encodeUtf8 : String -> ByteString

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Data.ByteString as ByteString #-}
{-# FOREIGN GHC import qualified Data.ByteString.Char8 as Char8 #-}
{-# FOREIGN GHC import qualified Data.Text.Encoding as Text #-}
{-# FOREIGN GHC import Data.ByteString (ByteString) #-}
{-# COMPILE GHC ByteString = type ByteString #-}
{-# COMPILE GHC null = ByteString.null #-}
{-# COMPILE GHC putStrLn = Char8.putStrLn #-}
{-# COMPILE GHC encodeUtf8 = Text.encodeUtf8 #-}
