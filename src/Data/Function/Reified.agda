module Data.Function.Reified where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Gen.Class
open import Data.List as List using ()
open import Data.String.Show
open import Data.Map as Map using (Map)

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
data _:->_ : Type -> Type -> Type where
  identity : a :-> a
  constant : a -> (b :-> a)
  fromMap : {{Ord a}} -> Map a b -> b -> a :-> b

applyFun : a :-> b -> a -> b
applyFun identity x = x
applyFun (constant x) _ = x
applyFun (fromMap m d) x = fromMaybe (Map.lookup x m) d