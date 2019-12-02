{-# OPTIONS --type-in-type #-}

module Control.Monad.RWS where

open import Control.Category
open import Data.Functor
open import Data.Product

-- RWS combines Reader, Writer and State.
RWS : Set -> Set -> Set -> Set -> Set
RWS R W S X = R -> S -> W -> X * S * W

instance
  -- RWS R W S is a functor.
  Functor:RWS : {R W S : Set} -> Endofunctor Sets (RWS R W S)
  Functor:RWS .map f compute r s w = 
    let (x , s' , w') = compute r s w
    in (f x , s' , w')
