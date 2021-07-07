{-# OPTIONS --type-in-type #-}

module Control.Monad.Normal where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b r : Type
    C t : Type -> Type

-------------------------------------------------------------------------------
-- NM
-------------------------------------------------------------------------------

data NM (C t : Type -> Type) (a : Type) : Type where
  Return : a -> NM C t a
  Bind : {{_ : C b}} -> t b -> (b -> NM C t a) -> NM C t a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-NM : Functor (NM C t)
  Functor-NM .map f (Return x) = Return (f x)
  Functor-NM .map f (Bind m k) = Bind m (\ b -> map f (k b))

  Applicative-NM : Applicative (NM C t)
  Applicative-NM .pure = Return
  Applicative-NM ._<*>_ (Return f) xs = map f xs
  Applicative-NM ._<*>_ (Bind m k) xs = Bind m (\ b -> k b <*> xs)

  Monad-NM : Monad (NM C t)
  Monad-NM ._>>=_ (Return x) k = k x
  Monad-NM ._>>=_ (Bind m h) k = Bind m (\ b -> h b >>= k)

-------------------------------------------------------------------------------
-- Utility functions
-------------------------------------------------------------------------------

liftNM : {{_ : C a}} -> t a -> NM C t a
liftNM m = Bind m Return

foldNM : (a -> r)
  -> (forall {b} {{_ : C b}} -> t b -> (b -> r) -> r)
  -> NM C t a
  -> r
foldNM {a = a} {r = r} {C = C} {t = t} ret bind = foldNM'
  where
    foldNM' : NM C t a -> r
    foldNM' (Return x) = ret x
    foldNM' (Bind m k) = bind m (\ b -> foldNM' (k b))

lowerNM : (a -> t a)
  -> (forall {b} {{_ : C b}} -> t b -> (b -> t a) -> t a)
  -> NM C t a
  -> t a
lowerNM = foldNM
