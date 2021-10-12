{-# OPTIONS --type-in-type #-}

module Control.Recursion.General where

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
  end : a -> General c r a
  more : (x : c) -> (r x -> General c r a) -> General c r a

foldGeneral : (a -> b) -> ((x : c) -> (r x -> b) -> b) -> General c r a -> b
foldGeneral done step = \ where
  (end x) -> done x
  (more x k) -> step x \ y -> foldGeneral done step (k y)

private
  bindGeneral : General c r a -> (a -> General c r b) -> General c r b
  bindGeneral m k = foldGeneral k more m

interpretGeneral : {{Monad m}}
  -> (t : (x : c) -> m (r x)) -> General c r a -> m a
interpretGeneral t = foldGeneral pure \ x -> t x >>=_

already : General c r a -> Maybe a
already = interpretGeneral \ _ -> nothing

instance
  Functor-General : Functor (General c r)
  Functor-General .map f = foldGeneral (end <<< f) more

  Applicative-General : Applicative (General c r)
  Applicative-General .pure = end
  Applicative-General ._<*>_ fs xs = bindGeneral fs \ f -> map (f $_) xs

  Monad-General : Monad (General c r)
  Monad-General ._>>=_ = bindGeneral

-------------------------------------------------------------------------------
-- DRec, Rec
-------------------------------------------------------------------------------

DRec : (c : Set) -> (c -> Set) -> Set
DRec c r = (x : c) -> General c r (r x)

Rec : Set -> Set -> Set
Rec a b = DRec a (const b)

call : DRec c r
call x = more x end

expand : DRec c r -> General c r a -> General c r a
expand f = interpretGeneral f

engine : DRec c r -> Nat -> General c r a -> General c r a
engine f 0 = id
engine f (suc n) fx = engine f n (expand f fx)

petrol : DRec c r -> Nat -> (x : c) -> Maybe (r x)
petrol f n x = already (engine f n (f x))

{-# TERMINATING #-}
combust : DRec c r -> (x : c) -> r x
combust {c} {r} f x = loop (f x)
  where
    loop : General c r (r x) -> r x
    loop y = maybe (loop (expand f y)) id (already y)
