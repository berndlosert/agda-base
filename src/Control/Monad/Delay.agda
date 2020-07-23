{-# OPTIONS --type-in-type #-}

module Control.Monad.Delay where

open import Prelude

open import Control.Size
open import Control.Thunk

private
  variable
    a b : Set
    i : Size

-- Delay represents processes which may always eventually yield. It is the
-- final coalgebra of the functor a +_.
data Delay (i : Size) (a : Set) : Set where
  Now : a -> Delay i a
  Later : Thunk i Delay a -> Delay i a

-- Since Delay is a final coalgebra, it has an unfold operation.
unfold : (b -> a + b) -> b -> Delay i a
unfold f y = either Now (λ x -> Later λ where .force -> unfold f x) $ f y

-- A process that never yields a value.
never : Delay i a
never = unfold (λ _ -> Right unit) unit

-- Run a process for at most n steps.
runFor : Nat -> Delay _ a -> Maybe a
runFor _ (Now x) = Just x
runFor Zero (Later _) = Nothing
runFor (Suc n) (Later thunk) = runFor n (force thunk)

-- Wrap a value x in a process that requires one step to yield x.
delay : a -> Delay _ a
delay x = unfold (λ b -> if b then Left x else Right True) False

-- Imagine a stream of Maybe a values. We model the stream as a function of
-- type Nat -> Maybe a. Assuming there is a least n : Nat such that the nth
-- element of the stream is a (Just x) value, tryMore will produce a Delay
-- value d such that runFor n d = Just x.
tryMore : (Nat -> Maybe a) -> Delay i a
tryMore {a = a} f = unfold try Zero
  where
    try : Nat -> a + Nat
    try n with f n
    ... | Just x = Left x
    ... | Nothing = Right (Suc n)

-- This is Just like tryMore, except that now we have a stream of Bool values,
-- modelled using a function of type Nat -> Bool.
minimize : (Nat -> Bool) -> Delay _ Nat
minimize test = tryMore (λ n -> if test n then Just n else Nothing)

instance
  functorDelay : Functor (Delay i)
  functorDelay .map f (Now x) = Now (f x)
  functorDelay .map f (Later x) =
    Later λ where .force -> map f (force x)

  applicativeDelay : Applicative (Delay i)
  applicativeDelay .pure = Now
  applicativeDelay ._<*>_ = λ where
    (Now f) (Now x) -> Now (f x)
    (Now f) x@(Later _) -> map f x
    (Later f) x@(Now _) -> Later λ where .force -> force f <*> x
    (Later f) (Later x) -> Later λ where .force -> force f <*> force x

  monadDelay : Monad (Delay i)
  monadDelay ._>>=_ (Now x) f = f x
  monadDelay ._>>=_ (Later x) f = Later λ where
    .force -> _>>=_ (force x) f
