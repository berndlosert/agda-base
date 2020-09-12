{-# OPTIONS --type-in-type #-}

module Network.Socket where

postulate
  Socket : Set

{-# FOREIGN GHC import Network.Socket #-}
{-# COMPILE GHC Socket = type Socket #-}
