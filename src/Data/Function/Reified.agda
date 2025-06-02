module Data.Function.Reified where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Gen.Class
open import Data.List as List using ()
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
      a b c : Type
      m : Type -> Type

-------------------------------------------------------------------------------
-- Reified functions
-------------------------------------------------------------------------------

infixr 5 _:->_
data _:->_ : Type -> Type -> Type
  identity : a :-> a
  constant : a -> Unit :-> a
  fromMap : {{Ord a}} -> Map a b -> b -> a :-> b

applyFun : a :-> b -> a -> b
applyFun (fun' graph default) x =
  case (List.head (List.filter ((_== x) <<< fst) graph)) \ where
    nothing -> default
    (just (_ , y)) -> y