module Control.Monad where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    m : Type -> Type

-------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

record Monad (m : Type -> Type) : Type where
  infixl 1 _>>=_
  field
    overlap {{Applicative-super}} : Applicative m
    _>>=_ : m a -> (a -> m b) -> m b

open Monad {{...}} public

module _ {{_ : Monad m}} where
  caseM : m a -> (a -> m b) -> m b
  caseM = _>>=_

  infixl 1 _=<<_
  _=<<_ : (a -> m b) -> m a -> m b
  _=<<_ = flip _>>=_

  infixl 4 _>>_
  _>>_ : m a -> m b -> m b
  _>>_ = _*>_

  infixr 1 _<=<_
  _<=<_ : (b -> m c) -> (a -> m b) -> a -> m c
  _<=<_ f g x = g x >>= f

  infixr 1 _>=>_
  _>=>_ : (a -> m b) -> (b -> m c) -> a -> m c
  _>=>_ = flip _<=<_

  join : m (m a) -> m a
  join = _>>= id

  liftM : (a -> b) -> m a -> m b
  liftM f x = do
    y <- x
    pure (f y)

  ap : m (a -> b) -> m a -> m b
  ap f x = do
    g <- f
    y <- x
    pure (g y)