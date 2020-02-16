{-# OPTIONS --type-in-type #-}

module Text.Show where

-- Conversion of values to readable Strings.

open import Data.String.Base

record Show (X : Set) : Set where
  constructor Show:
  field
    show : X -> String

open Show {{...}} public

-- Pretty-print Bool values.

open import Data.Bool

instance
  Show:Bool : Show Bool
  Show:Bool = Show: \ where
    true -> "true"
    false -> "false"

-- Pretty-print Int values.

open import Data.Int

instance
  Show:Int : Show Int
  Show:Int .show = Int.show

-- Pretty-print Nat values.

open import Data.Nat

instance
  Show:Nat : Show Nat
  Show:Nat .show n = Int.show (nonneg n)

-- Pretty-print String values.

open import Data.String

instance
  Show:String : Show String
  Show:String .show = String.show

-- Pretty-print pairs.

open import Data.Tuple

instance
  Show:Product : forall {X Y} {{_ : Show X}} {{_ : Show Y}} -> Show (X * Y)
  Show:Product = Show: \ where
    (Pair: x y) -> "Pair: " ++ show x ++ " " ++ show y

-- Pretty-print Maybe values.

open import Data.Maybe

instance
  Show:Maybe : {X : Set} {{_ : Show X}} -> Show (Maybe X)
  Show:Maybe = Show: \ where
    (just x) -> "just " ++ show x
    nothing -> "nothing"

-- Pretty-print lists.

open import Data.List

instance
  Show:List : forall {X} {{_ : Show X}} -> Show (List X)
  Show:List = Show: \ { [] -> "[]"; xs -> "[ " ++ csv xs ++ " ]" }
    where
      csv : {X : Set} {{_ : Show X}} -> List X -> String
      csv [] = ""
      csv (x :: []) = show x
      csv (x :: xs) = show x ++ " , " ++ csv xs

-- Pretty-print Fin values.

open import Data.Fin

instance
  Show:Fin : forall {n} -> Show (Fin (suc n))
  Show:Fin = Show: \ n -> show (Fin.toNat n)

-- Pretty-print Float values

open import Data.Float

instance
  Show:Float : Show Float
  Show:Float = Show: Float.toString
