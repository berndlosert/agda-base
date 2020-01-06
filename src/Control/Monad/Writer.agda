{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer where

-- Writer W X models computations of type X that store a value of type W. We
-- call such computations Writer computations.

open import Data.Tuple

Writer : Set -> Set -> Set
Writer W X = X * W

-- The tell function will produce a Writer computation that just stores the
-- given value.

open import Data.Unit

tell : forall {W} -> W -> Writer W Unit
tell w = (tt , w)

-- Simple handler of Writer W effects.

open import Control.Category
open import Data.Monoid

run : forall {W X} {{_ : Monoid W}}
  -> Writer W X -> X * W
run = id

-- If W is a monoid, then Writer W is a monad.

open import Control.Monad

instance
  Monad:Writer : forall {W} {{_ : Monoid W}} -> Monad Sets (Writer W)
  Monad:Writer .return x = (x , mempty)
  Monad:Writer .extend f (x , w) = let (y , w') = f x in (y , w <> w')
