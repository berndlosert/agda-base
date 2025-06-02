module Data.Stream where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad
open import Data.Monoid.Foldable
open import Data.List as List using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Stream
-------------------------------------------------------------------------------

data Stream (a : Type) : Type where
  _::_ : a -> Stream a -> Stream a

instance
  Functor-Stream : Functor Stream
  Functor-Stream .map f (x :: xs) = f x :: map f xs

  Applicative-Stream : Applicative Stream
  Applicative-Stream .pure x = x :: pure x
  Applicative-Stream ._<*>_ (f :: fs) (x :: xs) =
    f x :: (fs <*> xs)

  Monad-Stream : Monad Stream
  Monad-Stream ._>>=_ (x :: xs) k =
    case (k x) \ where
      (y :: _) -> y :: (xs >>= k)

  Comonad-Stream : Comonad Stream
  Comonad-Stream .extend f xs = pure (f xs)
  Comonad-Stream .extract (x :: xs) = x

iterate : (a -> a) -> a -> Stream a
iterate f x = x :: iterate f (f x)

unfold : (b -> Tuple a b) -> b -> Stream a
unfold f z = let (x , z') = f z in x :: unfold f z'

repeat : a -> Stream a
repeat = pure

prepend : List a -> Stream a -> Stream a
prepend [] ys = ys
prepend (x :: xs) ys = x :: prepend xs ys

take : Nat -> Stream a -> List a
take 0 _ = []
take (suc n) (x :: xs) = x :: take n xs

at : Nat -> Stream a -> a
at 0 (x :: _) = x
at (suc n) (x :: xs) = at n xs

cycle : List a -> Maybe (Stream a)
cycle [] = nothing
cycle {a} (x :: xs) = just (x :: go xs)
  where
    go : List a -> Stream a
    go [] = x :: go xs
    go (y :: ys) = y :: go ys

diag : Stream (Stream a) -> Stream a
diag = join
