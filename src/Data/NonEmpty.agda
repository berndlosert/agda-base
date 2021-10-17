{-# OPTIONS --type-in-type #-}

module Data.NonEmpty where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- NonEmptyness
-------------------------------------------------------------------------------

record NonEmptyness (a : Set) : Set where
  field nonempty : a -> Bool

open NonEmptyness {{...}} public

instance
  NonEmptyness-String : NonEmptyness String
  NonEmptyness-String .nonempty "" = false
  NonEmptyness-String .nonempty _ = true

  NonEmptyness-Maybe : NonEmptyness (Maybe a)
  NonEmptyness-Maybe .nonempty = isJust

  NonEmptyness-List : NonEmptyness (List a)
  NonEmptyness-List .nonempty [] = false
  NonEmptyness-List .nonempty _ = true

-------------------------------------------------------------------------------
-- NonEmpty
-------------------------------------------------------------------------------

record NonEmpty (a : Set) {{_ : NonEmptyness a}} : Set where
  constructor anNonEmpty
  field
    fromNonEmpty : a
    {{Assert-nonempty}} : Assert (nonempty fromNonEmpty)

open NonEmpty
