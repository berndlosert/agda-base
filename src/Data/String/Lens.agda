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

packed : Iso' (List Char) String
packed = iso String.pack String.unpack

unpacked : Iso' String (List Char)
unpacked = iso String.unpack String.pack

worded : Traversal' String String
worded f str = (| String.unwords (traverse f (String.words str)) |)

lined : Traversal' String String
lined f str = (| String.unlines (traverse f (String.lines str)) |)
