{-# OPTIONS --type-in-type #-}

module Network.Socket.ByteString where

open import Prelude

open import Data.ByteString
open import Network.Socket

postulate
  send : Socket -> ByteString -> IO Int

{-# FOREIGN GHC import Network.Socket.ByteString #-}
{-# COMPILE GHC send = send #-}
