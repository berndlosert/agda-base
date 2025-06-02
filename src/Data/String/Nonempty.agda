module Data.String.Nonempty where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Nonempty
open import Data.String.Show

-------------------------------------------------------------------------------
-- String1
-------------------------------------------------------------------------------

abstract
  String1 : Type
  String1 = String

  fromString1 : String1 -> String
  fromString1 s = s

  private
    toString1 : String -> String1
    toString1 s = s

instance
  FromString-String1 : FromString String1
  FromString-String1 .FromString.Constraint "" = Void
  FromString-String1 .FromString.Constraint _ = Unit
  FromString-String1 .fromString s = toString1 s

  Eq-String1 : Eq String1
  Eq-String1 ._==_ s t = fromString1 s == fromString1 t

  Ord-String1 : Ord String1
  Ord-String1 ._<_ s t = fromString1 s < fromString1 t

  Semigroup-String1 : Semigroup String1
  Semigroup-String1 ._<>_ s t = toString1 (fromString1 s <> fromString1 t)

  Nonemptiness-String : Nonemptiness String
  Nonemptiness-String .Nonempty = String1
  Nonemptiness-String .nonempty "" = nothing
  Nonemptiness-String .nonempty s = just (toString1 s)

  Show-String1 : Show String1
  Show-String1 .show s = show (fromString1 s)
  Show-String1 .showsPrec = showsPrecDefault  