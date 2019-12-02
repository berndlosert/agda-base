{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer where

open import Control.Category
open import Control.Monad
open import Data.Functor
open import Data.Semigroup
open import Data.Monoid
open import Data.Product
open import Data.Unit

-- Writer W X models computations of type X that store a value of type W.
-- We call such computations Writer computations.
Writer : Set -> Set -> Set
Writer W X = X * W

-- We use execWriter to get output of a Writer computation.
execWriter : {W X : Set} -> Writer W X -> X
execWriter = fst

instance
  -- Writer W is a functor.
  Functor:Writer : {W : Set} -> Endofunctor Sets (Writer W)
  Functor:Writer .map f (x , w) = (f x , w)

  -- If W is a monoid, then Writer W is a monad. The return function in this case
  -- produces a Writer computation that stores mempty. The bind operation
  -- essentially does function application while combining the stored values
  -- using the monoid operation.
  Monad:Writer : {W : Set} {{_ : Monoid W}} -> Monad Sets (Writer W)
  Monad:Writer .join ((x , w) , w') = (x , w <> w')
  Monad:Writer .return x = (x , mempty)

-- The tell function will produce a Writer computation that just stores the
-- given value.
tell : {W : Set} -> W -> Writer W Unit
tell w = (tt , w)
