{-# OPTIONS --type-in-type #-}

module Control.Monad.Free where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    f g m : Type -> Type

-------------------------------------------------------------------------------
-- Free
-------------------------------------------------------------------------------

record Free (f : Type -> Type) (a : Type) : Type where
  constructor Free:
  field runFree : {{_ : Monad m}} -> (forall {b} -> f b -> m b) -> m a

open Free

liftFree : f a -> Free f a
liftFree x = Free: \ t -> t x

interpretFree : {{_ : Monad m}}
  -> (forall {a} -> f a -> m a) -> Free f b -> m b
interpretFree t free = runFree free t

retractFree : {{_ : Monad m}} -> Free m a -> m a
retractFree = interpretFree id

instance
  Functor-Free : Functor (Free f)
  Functor-Free .map f free = Free: (map f <<< runFree free)

  Applicative-Free : Applicative (Free f)
  Applicative-Free .pure x = Free: \ _ -> return x
  Applicative-Free ._<*>_ f x = Free: \ t -> runFree f t <*> runFree x t

  Monad-Free : Monad (Free f)
  Monad-Free ._>>=_ m f = Free: \ t ->
    join (map (interpretFree t <<< f) (interpretFree t m))

-- Free forms a functor on the category Types ^ Types whose map operation is:
hoistFree : (forall {a} -> f a -> g a) -> Free f b -> Free g b
hoistFree t free = interpretFree (liftFree <<< t) free

-- Free also forms a monad on Types ^ Types. The return operation of this monad
-- is liftFree; the bind operation is defined below:
bindFree : Free f a -> (forall {b} -> f b -> Free g b) -> Free g a
bindFree free t = runFree free t

-- Free is a free construction. It is basically the left-adjoint of the
-- would-be forgetful functor U that forgets the monad structure of a functor.
-- The right adjunct of this adjunction is basically interpretFree. The left
-- adjunct is given below.
uninterpretFree : (forall {a} -> Free f a -> m a) -> f b -> m b
uninterpretFree t x = t (liftFree x)

-- When F is a functor, Free F A is an F-algebra for any type A. The operation
-- of this algebra is:
impure : f (Free f a) -> Free f a
impure op = join (liftFree op)

-- A fold operation based on the Kleisli triple definition of monad.
foldFree : (a -> b) -> (forall {c} -> (c -> b) -> f c -> b) -> Free f a -> b
foldFree {f = f} ret ext free = interpretFree t free ret ext
  where

    -- M is the free monad generated by F based on Church encoding of the
    -- Kleisli triple definition of monad.
    M : Type -> Type
    M a = forall {b}
      -> (a -> b)
      -> (forall {c} -> (c -> b) -> f c -> b)
      -> b

    instance
      Functor-M : Functor M
      Functor-M .map f m = \ ret ext -> m (ret <<< f) ext

      Applicative-M : Applicative M
      Applicative-M .pure x = \ ret ext -> ret x
      Applicative-M ._<*>_ f x = \ ret ext ->
        f (\ g -> x (ret <<< g) ext) ext

      Monad-M : Monad M
      Monad-M ._>>=_ m f = \ ret ext -> m (\ y -> (f y) ret ext) ext

    -- The liftFree operation of the free monad M.
    t : f a -> M a
    t x = \ ret ext -> ext ret x

-- A fold operation based on the standard definition of monad. This one
-- requires F to be a functor.
foldFree' : {{_ : Functor f}} -> (a -> b) -> (f b -> b) -> Free f a -> b
foldFree' {f = f} {{inst}} ret jn free = interpretFree t free ret jn
  where

    -- M is the free monad generated by F based on Church encoding of the
    -- standard definition of monad.
    M : Type -> Type
    M a = forall {b} -> (a -> b) -> (f b -> b) -> b

    instance
      Functor-M : Functor M
      Functor-M .map f m = \ ret jn -> m (ret <<< f) jn

      Applicative-M : Applicative M
      Applicative-M .pure x = \ ret jn -> ret x
      Applicative-M ._<*>_ f x = \ ret jn ->
        f (\ g -> x (ret <<< g) jn) jn

      Monad-M : Monad M
      Monad-M ._>>=_ m f = \ ret jn -> m (\ x -> (f x) ret jn) jn

    -- The liftFree operation of the free monad M.
    t : f a -> M a
    t x = \ ret jn -> jn ((map {{inst}} ret) x)
