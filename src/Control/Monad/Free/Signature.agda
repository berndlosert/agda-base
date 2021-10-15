{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Signature where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Recursion
open import Data.Dictionary

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
  MonadDict-Free : Dict Monad (Free sig)
  MonadDict-Free .return x = finished x absurd
  MonadDict-Free .bind (finished x _) k = k x
  MonadDict-Free .bind (roll symb arg) k =
    let arg' x = MonadDict-Free .bind (toFree (arg x)) k
    in inn (operation symb arg')

instance
  Monad-Free : Monad (Free sig)
  Monad-Free = fromDict MonadDict-Free

  Applicative-Free : Applicative (Free sig)
  Applicative-Free = Monad-Free .Applicative-super

  Functor-Free : Functor (Free sig)
  Functor-Free = Applicative-Free .Functor-super
