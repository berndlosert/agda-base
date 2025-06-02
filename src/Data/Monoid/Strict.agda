module Data.Monoid.Strict where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.Endo
open import Data.Semigroup.FromMaybe

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Wrapper for Endo and FromMaybe needed for foldl and foldl1
-------------------------------------------------------------------------------

record Strict (a : Type) : Type where
  constructor asStrict
  field getStrict : a

open Strict public

instance
  Semigroup-Strict-FromMaybe : Semigroup (Strict (FromMaybe a))
  Semigroup-Strict-FromMaybe ._<>_ (asStrict (asFromMaybe g)) (asStrict (asFromMaybe f)) = 
    asStrict $ asFromMaybe $ \ where
      nothing -> g (just $! f nothing)
      (just x)  -> g (just $! f (just x))

  Semigroup-Strict-Endo : Semigroup (Strict (Endo a))
  Semigroup-Strict-Endo ._<>_ (asStrict (asEndo g)) (asStrict (asEndo f)) = asStrict (asEndo (\ x -> g $! f x))

  Monoid-Strict-Endo : Monoid (Strict (Endo a))
  Monoid-Strict-Endo .mempty = asStrict (asEndo id)