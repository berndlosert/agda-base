{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer.Class where

open import Prelude

private variable A B : Set

record MonadWriter (W : Set) (M : Set -> Set) : Set where
  field
    {{monoid}} : Monoid W
    {{monad}} : Monad M
    tell : W -> M Unit
    listen : M A -> M (Tuple A W)
    pass : M (Tuple A (W -> W)) -> M A

  writer : Tuple A W -> M A
  writer (a , w) = do
    tell w
    return a

  listens : (W -> B) -> M A -> M (Tuple A B)
  listens f m = do
    (a , w) <- listen m
    return (a , f w)

  censor : (W -> W) -> M ~> M
  censor f m = pass do
    a <- m
    return (a , f)

open MonadWriter {{...}} public
