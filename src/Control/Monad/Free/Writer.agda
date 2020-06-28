{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer where

-- Writer W X models computations of type X that store a value of type W. We
-- call such computations Writer computations.

open import Data.Pair

Writer : Set -> Set -> Set
Writer W X = X * W

-- Writer W is a functor. The proof is provided by Endofunctor:Product.

open import Data.Functor

-- The tell function will produce a Writer computation that just stores the
-- given value.

import Control.Monad.Eff as Eff
open Eff using (Eff)
open import Data.Functor.Union
open import Data.Unit

tell : forall {W Fs} {{_ : Member (Writer W) Fs}} -> W -> Eff Fs Unit
tell w = Eff.send (tt , w)

-- Simple handler of Writer W effects.

open import Control.Category
open import Control.Monad
open import Control.Monad.Free
open import Data.Monoid

run : forall {W Fs X} {{_ : Monoid W}}
  -> Eff (Writer W :: Fs) X -> Eff Fs (X * W)
run = Eff.fold
  (return ∘ (_, empty))
  (\ { k (x , w) -> map (second (w <>_)) (k x) })

-- If W is a monoid, then Writer W is a monad. The return function in this case
-- produces a Writer computation that stores empty. The bind operation
-- essentially does function application while combining the stored values
-- using the monoid operation.

--instance
--  monadWriter : forall {W} {{_ : Monoid W}} -> Monad (Writer W)
--  monadWriter = record {
--      instance:Functor = functorWriter;
--      join = \ { ((x , w) , w') -> (x , w <> w') };
--      return = \ x -> (x , empty)
--    }
