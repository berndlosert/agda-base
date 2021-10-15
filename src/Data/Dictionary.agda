{-# OPTIONS --type-in-type #-}

module Data.Dictionary where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- Dictionary
-------------------------------------------------------------------------------

record Dictionary {k : Set} (p : k -> Set) : Set where
  field
    Dict : (q : k -> Set) -> {{q === p}} -> k -> Set
    toDict : {a : k} -> p a -> Dict p a
    fromDict : {a : k} -> Dict p a -> p a

open Dictionary {{...}} public

-------------------------------------------------------------------------------
-- SemigroupDict
-------------------------------------------------------------------------------

record SemigroupDict (a : Set) : Set where
  field combine : a -> a -> a

open SemigroupDict public

instance
  Dictionary-Semigroup : Dictionary Semigroup
  Dictionary-Semigroup .Dict _ = SemigroupDict
  Dictionary-Semigroup .toDict sg .combine = sg ._<>_
  Dictionary-Semigroup .fromDict dict ._<>_ = dict .combine

-------------------------------------------------------------------------------
-- MonadDict
-------------------------------------------------------------------------------

record MonadDict (m : Set -> Set) : Set where
  field
    return : a -> m a
    bind : m a -> (a -> m b) -> m b

  liftM : (a -> b) -> m a -> m b
  liftM f mx = bind mx (f >>> return)

  ap : m (a -> b) -> m a -> m b
  ap mf mx = bind mf \ f -> bind mx \ x -> return (f x)

open MonadDict public

instance
  Dictionary-Monad : Dictionary Monad
  Dictionary-Monad .Dict _ = MonadDict
  Dictionary-Monad .toDict mnd .return = mnd .Applicative-super .pure
  Dictionary-Monad .toDict mnd .bind = mnd ._>>=_
  Dictionary-Monad .fromDict dict .Applicative-super .Functor-super .map = liftM dict
  Dictionary-Monad .fromDict dict .Applicative-super .pure = return dict
  Dictionary-Monad .fromDict dict .Applicative-super ._<*>_ = ap dict
  Dictionary-Monad .fromDict dict ._>>=_ = bind dict
