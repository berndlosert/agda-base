{-# OPTIONS --type-in-type #-}

module Data.String.Lens where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Lens
open import Data.String as String using ()
open import Data.Traversable

-------------------------------------------------------------------------------
-- String optics
-------------------------------------------------------------------------------

worded : Simple Traversal String String
worded f str = (| String.unwords (traverse f (String.words str)) |)

lined : Simple Traversal String String
lined f str = (| String.unlines (traverse f (String.lines str)) |)

instance
  Cons-String : Cons String String Char Char
  Cons-String .#Cons = prism' (uncurry String.cons) String.uncons
