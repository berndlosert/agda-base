{-# OPTIONS --type-in-type #-}

module Control.Monad.RWS where

-- RWS combines Reader, Writer and State.

open import Data.Product

RWS : Set -> Set -> Set -> Set -> Set
RWS R W S X = R -> S -> W -> X * S * W

-- RWS R W S is a functor.

open import Control.Category
open import Data.Functor

instance
  Functor:RWS : {R W S : Set} -> Endofunctor Sets (RWS R W S)
  Functor:RWS .map f compute r s w =
    let (x , s' , w') = compute r s w
    in (f x , s' , w')
