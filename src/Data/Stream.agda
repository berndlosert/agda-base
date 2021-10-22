module Data.Stream where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad
open import Data.Foldable
open import Data.List as List using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- Stream
-------------------------------------------------------------------------------

data Stream (a : Set) : Set where
  _::_ : a -> Inf (Stream a) -> Stream a

instance
  Functor-Stream : Functor Stream
  Functor-Stream .map f (x :: xs) = f x :: sharp (map f (flat xs))

  Applicative-Stream : Applicative Stream
  Applicative-Stream .pure x = x :: sharp (pure x)
  Applicative-Stream ._<*>_ (f :: fs) (x :: xs) =
    f x :: sharp (flat fs <*> flat xs)

  Comonad-Stream : Comonad Stream
  Comonad-Stream .extend f xs = pure (f xs)
  Comonad-Stream .extract (x :: xs) = x

iterate : (a -> a) -> a -> Stream a
iterate f x = x :: sharp (iterate f (f x))

unfold : (b -> Pair a b) -> b -> Stream a
unfold f z = let (x , z') = f z in x :: sharp (unfold f z')

repeat : a -> Stream a
repeat = pure

prepend : List a -> Stream a -> Stream a
prepend [] ys = ys
prepend (x :: xs) ys = x :: sharp (prepend xs ys)

take : Nat -> Stream a -> List a
take 0 _ = []
take (suc n) (x :: xs) = x :: take n (flat xs)

at : Nat -> Stream a -> a
at 0 (x :: _) = x
at (suc n) (x :: xs) = at n (flat xs)

cycle : (xs : List a) -> {{Assert $ not (null xs)}} -> Stream a
cycle [] = panic "Data.Stream.cycle: bad argument"
cycle {a} (x :: xs) = x :: sharp (cycle' xs)
  where
    cycle' : List a -> Stream a
    cycle' [] = x :: sharp (cycle' xs)
    cycle' (y :: ys) = y :: sharp (cycle' ys)
