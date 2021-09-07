{-# OPTIONS --type-in-type #-}

open import Prelude

open import Data.List as List using ()

reverseTest : List.reverse ('a' :: 'b' :: 'c' :: []) === 'c' :: 'b' :: 'a' :: []
reverseTest = Refl
