module Data.Functor.Product.Nary where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.List.Elem

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    k : Set
    a : k
    f g : k -> Set
    fs gs : List (k -> Set)

-------------------------------------------------------------------------------
-- ProductN
-------------------------------------------------------------------------------

data ProductN : List (k -> Set) -> k -> Set where
  nil : ProductN [] a
  cons : f a -> ProductN fs a -> ProductN (f :: fs) a

project : Elem f fs -> ProductN fs a -> f a
project {fs = []} elem _ = absurd elem
project {fs = g :: gs} (elemPos 0) (cons h _) = unsafeCoerce h
project {f = f} (elemPos (suc n)) (cons _ t) =
  let
    elem' : Elem f _
    elem' = elemPos n
  in
    project elem' t
