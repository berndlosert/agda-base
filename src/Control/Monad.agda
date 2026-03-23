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

open Monad {{...}} public

instance
  Monad-Function : Monad (Function a)
  Monad-Function ._>>=_ f g x = g (f x) x

  Monad-Identity : Monad Identity
  Monad-Identity ._>>=_ x k = k (runIdentity x)

  Monad-Maybe : Monad Maybe
  Monad-Maybe ._>>=_ nothing _ = nothing
  Monad-Maybe ._>>=_ (just x) k = k x

  Monad-List : Monad List
  Monad-List ._>>=_ [] k = []
  Monad-List ._>>=_ (x :: xs) k = k x <> (xs >>= k)    
    
  Monad-Either : Monad (Either a)
  Monad-Either ._>>=_ (left x) _ = left x
  Monad-Either ._>>=_ (right x) k = k x

  Monad-Tuple : {{Monoid a}} -> Monad (Tuple a)
  Monad-Tuple ._>>=_ (u , x) k = let (v , y) = k x in (u <> v , y)