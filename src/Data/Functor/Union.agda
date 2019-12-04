{-# OPTIONS --type-in-type #-}

module Data.Functor.Union where

-- Union is a higher-order generalization of Either. To be precise,
-- Union [ F1 # ... # Fn ] X is the disjoint union F1 X + ... + Fn X.

open import Data.List.Base public
open import Data.Either public
open import Data.Void public

Union : List (Set -> Set) -> Set -> Set
Union [] X = Void
Union (F :: Fs) X = F X + Union Fs X

-- We need generalizations of the injections left and right and projections
-- leftToMaybe and rightToMaybe for Union. These generalizations are provided
-- by the following Member type class.

open import Control.Category
open import Data.Functor
open import Data.Maybe.Base

record Member (F : Set -> Set) (Fs : List (Set -> Set)) : Set where
  field
    inj : F ~> Union Fs
    prj : Union Fs ~> Maybe <<< F

open Member {{...}} public

instance
  Member:Cons : forall {F Fs} -> Member F (F :: Fs)
  Member:Cons .inj = left
  Member:Cons .prj (left x) = just x
  Member:Cons .prj (right u) = nothing

-- If the Fs are functors, then so is Union Fs. The proof for the case Fs = []
-- is given by Functor:const Void. The proof for the nonempty Fs case is
-- Endofunctor:Coproduct instance.
