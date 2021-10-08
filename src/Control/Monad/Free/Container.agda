{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Container where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Container
open import Data.Fix

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    c : Container

-------------------------------------------------------------------------------
-- Free
-------------------------------------------------------------------------------

Free : Container -> Set -> Set
Free c a = Fix $ Sum (Const a) c

inn : Extension c (Free c a) -> Free c a
inn (extension s p) = toFix (extension (right s) p)

private
  pureFree : a -> Free c a
  pureFree x = toFix (extension (left x) \ ())

  bindFree : Free c a -> (a -> Free c b) -> Free c b
  bindFree (toFix (extension (left x) _)) k = k x
  bindFree (toFix (extension (right s) p)) k =
    inn (extension s (\ x -> bindFree (p x) k))

instance
  Functor-Free : Functor (Free c)
  Functor-Free .map f xs = bindFree xs (pureFree <<< f)

  Applicative-Free : Applicative (Free c)
  Applicative-Free .pure = pureFree
  Applicative-Free ._<*>_ fs xs = bindFree fs \ f -> map (f $_) xs

  Monad-Free : Monad (Free c)
  Monad-Free ._>>=_ = bindFree
