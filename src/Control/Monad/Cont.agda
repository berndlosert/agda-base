{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont where

-- Cont X Y is the type of continuation handlers for continuations of type
-- Y -> X. It is used for doing CPS programming. For example, given a function
-- f : W -> Y whose output is being consumed by functions of type Y -> X, we
-- can change f into a CPS function f' : W -> Cont X Y that on input w
-- returns a continuation handler h that on input k : Y -> X (a continuation),
-- returns k (f w).

Cont : Set -> Set -> Set
Cont X Y = (Y -> X) -> X

-- Cont X forms a functor.

open import Data.Functor public

instance
  Functor:Cont : forall {X} -> Functor Sets Sets (Cont X)
  Functor:Cont .map f h = \ k -> h (f >>> k)

-- Cont X forms a monad.

open import Control.Monad public
open import Data.Function public

instance
  Monad:Cont : forall {X} -> Monad Sets (Cont X)
  Monad:Cont .return x = _$ x
  Monad:Cont .extend k m = \ c -> m (\ x -> (k x) c)

-- The infamous call-with-current-continuation.

open import Data.Void

callCC : forall {X Y} -> ((Y -> Cont X Void) -> Cont X Y) -> Cont X Y
callCC h = \ k -> h (\ y -> const (k y)) k

-- Operators for delimited continuations.

reset : forall {X Y} -> Cont X X -> Cont Y X
reset h k = k (h id)

shift : forall {X Y} -> ((X -> Y) -> Cont Y Y) -> Cont Y X
shift f k = (f k) id
