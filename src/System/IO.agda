{-# OPTIONS --type-in-type #-}

module System.IO where

open import Prelude

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStrLn (f s)
