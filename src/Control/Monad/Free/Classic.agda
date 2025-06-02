module Control.Monad.Free.Classic where

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

data Free (f : Type -> Type) (a : Type) : Type where
  var : a -> Free f a
  op : f (Free f a) -> Free f a

instance
  Functor-Free : {{Functor f}} -> Functor (Free f)
  Functor-Free .map f (var x) = var (f x)
  Functor-Free .map f (op g) = op (map (map f) g)

  Applicative-Free : {{Functor f}} -> Applicative (Free f)
  Applicative-Free ._<*>_ (var f) x = map f x
  Applicative-Free ._<*>_ (op f) x = op (map (_<*> x) f)
  Applicative-Free .pure = var

  Monad-Free : {{Functor f}} -> Monad (Free f)
  Monad-Free ._>>=_ (var x) k = k x
  Monad-Free ._>>=_ (op x) k = op (map (_>>= k) x)