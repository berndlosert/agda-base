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
inn (Extension: s p) = Fix: (Extension: (Right s) p)

private
  pureFree : a -> Free c a
  pureFree x = Fix: (Extension: (Left x) \ ())

  bindFree : Free c a -> (a -> Free c b) -> Free c b
  bindFree (Fix: (Extension: (Left x) _)) k = k x
  bindFree (Fix: (Extension: (Right s) p)) k =
    inn (Extension: s (\ x -> bindFree (p x) k))

instance
  Functor-Free : Functor (Free c)
  Functor-Free .map f xs = bindFree xs (pureFree <<< f)

  Applicative-Free : Applicative (Free c)
  Applicative-Free .pure = pureFree
  Applicative-Free ._<*>_ fs xs = bindFree fs \ f -> map (f $_) xs

  Monad-Free : Monad (Free c)
  Monad-Free ._>>=_ = bindFree
