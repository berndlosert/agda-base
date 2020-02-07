{-# OPTIONS --type-in-type #-}

module Control.Monad.Freer where

-- A higher-order version of Free.

open import Control.Monad public

module Freer where

  record Freer
      (F : (Set -> Set) -> Set -> Set)
      (T : Set -> Set)
      (X : Set)
      : Set
    where
      constructor Freer:
      field
        run : forall {M} {{_ : Monad Sets^Sets M}} -> (F ~> M) -> M T X

  open Freer

  lift : forall {F} -> F ~> Freer F
  lift x = Freer: \ t -> t x

  interpret : forall {F M} {{_ : Monad Sets^Sets M}}
    -> (F ~> M) -> Freer F ~> M
  interpret t freer = run freer t

  -- This is the left inverse (retract) of lift.

  lower : forall {M} {{_ : Monad Sets^Sets M}} -> Freer M ~> M
  lower = interpret id

  -- Freer F is a functor.

  instance
    Functor:Freer : forall {F} -> Endofunctor Sets^Sets (Freer F)
    Functor:Freer .map f freer =
      Freer: (hmap f <<< run freer)

  -- Freer F is a monad.

  instance
    Monad:Freer : forall {F} -> Monad Sets^Sets (Freer F)
    Monad:Freer .return x = Freer: \ _ -> return x
    Monad:Freer .extend f m = Freer: \ t ->
      join (hmap (interpret t <<< f) (interpret t m))

  -- Free forms a functor on the category Sets ^ Sets whose map operation is:

  hoist : forall {F G} -> (F ~> G) -> Freer F ~> Freer G
  hoist t freer = interpret (lift <<< t) freer

  -- Freer also forms a monad on Sets^Sets ^ Sets^Sets. The return operation of
  -- this monad is lift; the extend operation is defined below:

  flatMap : forall {F G} -> (F ~> Freer G) -> Freer F ~> Freer G
  flatMap = interpret

  -- Freer is a free construction. It is basically the left-adjoint of the
  -- would-be forgetful functor U that forgets the monad structure of a functor.
  -- The right adjunct of this adjunction is basically interpret. The left
  -- adjunct is given below.

  uninterpret : forall {F M} -> (Freer F ~> M) -> F ~> M
  uninterpret t x = t (lift x)

  -- No comment.

  impure : forall {F T X} -> F (Freer F T) X -> Freer F T X
  impure op = join (lift op)
