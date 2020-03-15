{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Classes where

open import Prelude

private
  variable
    A B : Set
    M : Set -> Set

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    lift : {{_ : Monad M}} -> M ~> T M
    transform : Monad M -> Monad (T M)

open MonadTrans {{...}} public

record MonadCont (M : Set -> Set) : Set where
  field
    {{Monad:MonadCont}} : Monad M
    callCC : ((A -> M B) -> M A) -> M A

open MonadCont {{...}} public

record MonadReader (R : Set) (M : Set -> Set) : Set where
  field
    {{Monad:MonadReader}} : Monad M
    ask : M R
    local : (R -> R) -> M ~> M

  asks : (R -> A) -> M A
  asks f = do
    r <- ask
    return (f r)

open MonadReader {{...}} public

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
