{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Signature where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Recursion

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
  constructor aFree
  field unFree : Fix (ConstS a + sig)

open Free public

pattern finished x arg = aFree (sup (left x) arg)
pattern roll symb arg = aFree (sup (right symb) arg)

inn : Operation sig (Free sig a) -> Free sig a
inn (operation symb arg) = roll symb (arg >>> unFree)

instance
  Monad-Free : Monad (Free sig)
  Monad-Free = mkMonad bind return
    where
      bind : Free sig a -> (a -> Free sig b) -> Free sig b
      bind (finished x _) k = k x
      bind (roll symb arg) k =
        let arg' x = bind (aFree (arg x)) k
        in inn (operation symb arg')

      return : a -> Free sig a
      return x = finished x absurd

  Applicative-Free : Applicative (Free sig)
  Applicative-Free = Monad-Free .Applicative-super

  Functor-Free : Functor (Free sig)
  Functor-Free = Applicative-Free .Functor-super
