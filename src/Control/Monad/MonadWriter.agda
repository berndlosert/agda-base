{-# OPTIONS --type-in-type #-}

module Control.Monad.MonadWriter where

open import Prelude

private
  variable
    A B : Set

record MonadWriter (W : Set) (M : Set -> Set) : Set where
  field
    {{Monoid:MonadWriter}} : Monoid W
    {{Monad:Monad}} : Monad M
    tell : W -> M Unit
    listen : M A -> M (A * W)
    pass : M (A * (W -> W)) -> M A

  writer : A * W -> M A
  writer (Pair: a w) = do
    tell w
    return a

  listens : (W -> B) -> M A -> M (A * B)
  listens f m = do
    (Pair: a w) <- listen m
    return (Pair: a (f w))

  censor : (W -> W) -> M ~> M
  censor f m = pass $ do
    a <- m
    return (Pair: a f)

open MonadWriter {{...}} public
