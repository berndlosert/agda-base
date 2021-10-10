{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Signature where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Signature
open import Data.Fix

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    sig : Signature

-------------------------------------------------------------------------------
-- Free
-------------------------------------------------------------------------------

Free : Signature -> Set -> Set
Free sig a = Fix (ConstS a + sig)

inn : Operation sig (Free sig a) -> Free sig a
inn (operation symb arg) = sup (right symb) arg

private
  pureFree : a -> Free sig a
  pureFree x = sup (left x) absurd

  bindFree : Free sig a -> (a -> Free sig b) -> Free sig b
  bindFree (sup (left x) _) k = k x
  bindFree (sup (right symb) arg) k =
    let arg' x = bindFree (arg x) k
    in inn (operation symb arg')

instance
  Functor-Free : Functor (Free sig)
  Functor-Free .map f xs = bindFree xs (pureFree <<< f)

  Applicative-Free : Applicative (Free sig)
  Applicative-Free .pure = pureFree
  Applicative-Free ._<*>_ fs xs = bindFree fs \ f -> map (f $_) xs

  Monad-Free : Monad (Free sig)
  Monad-Free ._>>=_ = bindFree
