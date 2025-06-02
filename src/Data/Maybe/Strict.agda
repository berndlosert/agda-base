module Data.Maybe.Strict where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (Maybe; just; nothing; maybe)

open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Maybe (strict)
-------------------------------------------------------------------------------

data Maybe (a : Type) : Type where
  just : a -> Maybe a
  nothing : Maybe a

maybe : b -> (a -> b)  -> Maybe a -> b
maybe _ f (just x) = f x
maybe x _ nothing = x

instance
    Show-Maybe : {{Show a}} -> Show (Maybe a)
    Show-Maybe .show = showDefault
    Show-Maybe .showsPrec prec = \ where
      (just x) -> showsUnaryWith showsPrec "just" prec x
      nothing -> "nothing"

{-# FOREIGN GHC data SMaybe a = SJust !a | SNothing #-}
{-# COMPILE GHC Maybe = data SMaybe (SJust | SNothing) #-}