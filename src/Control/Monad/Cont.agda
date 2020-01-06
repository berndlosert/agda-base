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

-- Cont X is also a monad. The Kleisli composition of this monad allows one
-- to compose functions in CPS style.

open import Control.Category
open import Control.Monad
open import Data.Function
open import Data.Functor

instance
  Monad:Cont : forall {X} -> Monad Sets (Cont X)
  Monad:Cont .return x = _$ x
  Monad:Cont .extend k m = \ c -> m (\ x -> (k x) c)

-- The infamous call-with-current-continuation.

callCC : forall {X Y Z} -> ((Z -> Cont X Y) -> Cont X Z) -> Cont X Z
callCC h k = h (\ x -> const (k x)) k

-- Operators for delimited continuations.

reset : forall {X Y} -> Cont X X -> Cont Y X
reset h k = k (h id)

shift : forall {X Y} -> ((X -> Y) -> Cont Y Y) -> Cont Y X
shift f k = (f k) id
