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

record Free (sig : Signature) (a : Set) : Set where
  constructor toFree
  field unFree : Fix (ConstS a + sig)

open Free public

pattern finished x arg = toFree (sup (left x) arg)
pattern roll symb arg = toFree (sup (right symb) arg)

inn : Operation sig (Free sig a) -> Free sig a
inn (operation symb arg) = roll symb (arg >>> unFree)

private
  pureFree : a -> Free sig a
  pureFree x = finished x absurd

  bindFree : Free sig a -> (a -> Free sig b) -> Free sig b
  bindFree (finished x _) k = k x
  bindFree (roll symb arg) k =
    let arg' x = bindFree (toFree (arg x)) k
    in inn (operation symb arg')

instance
  Functor-Free : Functor (Free sig)
  Functor-Free .map f xs = bindFree xs (pureFree <<< f)

  Applicative-Free : Applicative (Free sig)
  Applicative-Free .pure = pureFree
  Applicative-Free ._<*>_ fs xs = bindFree fs \ f -> map (f $_) xs

  Monad-Free : Monad (Free sig)
  Monad-Free ._>>=_ = bindFree
