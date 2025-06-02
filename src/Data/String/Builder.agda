module Data.String.Builder where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Builder
-------------------------------------------------------------------------------

postulate
  Builder : Type
  fromBuilder : Builder -> String
  toBuilder : String -> Builder
  singleton : Char -> Builder

private
  postulate
    builderEq : Builder -> Builder -> Bool
    builderLess : Builder -> Builder -> Bool
    builderAppend : Builder -> Builder -> Builder
    builderEmpty : Builder

instance
  Eq-Builder : Eq Builder
  Eq-Builder ._==_ = builderEq

  Ord-Builder : Ord Builder
  Ord-Builder ._<_ = builderLess

  Semigroup-Builder : Semigroup Builder
  Semigroup-Builder ._<>_ = builderAppend

  Monoid-Builder : Monoid Builder
  Monoid-Builder .mempty = builderEmpty

  FromString-Builder : FromString Builder
  FromString-Builder .FromString.Constraint _ = Unit
  FromString-Builder .fromString s = toBuilder s

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Data.Text.Lazy (toStrict) #-}
{-# FOREIGN GHC import Data.Text.Lazy.Builder #-}
{-# COMPILE GHC Builder = type Builder #-}
{-# COMPILE GHC fromBuilder = toStrict . toLazyText #-}
{-# COMPILE GHC toBuilder = fromText #-}
{-# COMPILE GHC singleton = singleton #-}
{-# COMPILE GHC builderEq = (==) #-}
{-# COMPILE GHC builderLess = (<) #-}
{-# COMPILE GHC builderAppend = (<>) #-}
{-# COMPILE GHC builderEmpty = mempty #-}
