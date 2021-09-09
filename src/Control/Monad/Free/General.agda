{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.General where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    r : c -> Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- General
-------------------------------------------------------------------------------

data General (c : Set) (r : c -> Set) (a : Set) : Set where
  gpure : a -> General c r a
  gbind : (x : c) -> (r x -> General c r a) -> General c r a

DFn : (c : Set) -> (c -> Set) -> Set
DFn c r = (x : c) -> General c r (r x)

Fn : Set -> Set -> Set
Fn a b = DFn a (const b)

general : (a -> b) -> ((x : c) -> (r x -> b) -> b) -> General c r a -> b
general pure bind = \ where
  (gpure x) -> pure x
  (gbind x k) -> bind x (\ y -> general pure bind (k y))

call : DFn c r
call x = gbind x gpure

private
  bindGeneral : General c r a -> (a -> General c r b) -> General c r b
  bindGeneral m k = general k gbind m

interpretGeneral : {{Monad m}}
  -> (t : (x : c) -> m (r x)) -> General c r a -> m a
interpretGeneral t = general pure \ x -> (t x >>=_)

already : General c r a -> Maybe a
already = interpretGeneral (\ _ -> nothing)

instance
  Functor-General : Functor (General c r)
  Functor-General .map f = general (gpure <<< f) gbind

  Applicative-General : Applicative (General c r)
  Applicative-General .pure = gpure
  Applicative-General ._<*>_ fs xs = bindGeneral fs \ f -> map (f $_) xs

  Monad-General : Monad (General c r)
  Monad-General ._>>=_ = bindGeneral

expand : DFn c r -> General c r a -> General c r a
expand f = interpretGeneral f

engine : DFn c r -> Nat -> General c r a -> General c r a
engine f 0 = id
engine f (suc n) = engine f n <<< expand f

petrol : DFn c r -> Nat -> (x : c) -> Maybe (r x)
petrol f n x = already $ engine f n $ f x
