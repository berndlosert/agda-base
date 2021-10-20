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
    a b r : Set
    C t : Set -> Set

-------------------------------------------------------------------------------
-- NM
-------------------------------------------------------------------------------

data NM (C t : Set -> Set) (a : Set) : Set where
  nmpure : a -> NM C t a
  nmbind : {{C b}} -> t b -> (b -> NM C t a) -> NM C t a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-NM : Functor (NM C t)
  Functor-NM .map f (nmpure x) = nmpure (f x)
  Functor-NM .map f (nmbind m k) = nmbind m (\ b -> map f (k b))

  Applicative-NM : Applicative (NM C t)
  Applicative-NM .pure = nmpure
  Applicative-NM ._<*>_ (nmpure f) xs = map f xs
  Applicative-NM ._<*>_ (nmbind m k) xs = nmbind m (\ b -> k b <*> xs)

  Monad-NM : Monad (NM C t)
  Monad-NM ._>>=_ (nmpure x) k = k x
  Monad-NM ._>>=_ (nmbind m h) k = nmbind m (\ b -> h b >>= k)

-------------------------------------------------------------------------------
-- Utility functions
-------------------------------------------------------------------------------

liftNM : {{C a}} -> t a -> NM C t a
liftNM m = nmbind m nmpure

foldNM : (a -> r)
  -> (forall {b} -> {{C b}} -> t b -> (b -> r) -> r)
  -> NM C t a
  -> r
foldNM {a = a} {r = r} {C = C} {t = t} ret bind = foldNM'
  where
    foldNM' : NM C t a -> r
    foldNM' (nmpure x) = ret x
    foldNM' (nmbind m k) = bind m (\ b -> foldNM' (k b))

lowerNM : (a -> t a)
  -> (forall {b} -> {{C b}} -> t b -> (b -> t a) -> t a)
  -> NM C t a
  -> t a
lowerNM = foldNM
