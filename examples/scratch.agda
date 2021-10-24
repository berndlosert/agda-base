open import Prelude as Prelude using (pure; _<*>_; Functor-super; map)

variable
  a b c : Set

record Monad (m : Set -> Set) : Set where
  infixl 1 _>>=_
  field
    overlap {{Applicative-super}} : Prelude.Applicative m
    _>>=_ : m a -> (a -> m b) -> m b
    return : a -> m a

  infixl 1 _=<<_
  _=<<_ : (a -> m b) -> m a -> m b
  _=<<_ = Prelude.flip _>>=_

  infixl 4 _>>_
  _>>_ : m a -> m b -> m b
  _>>_ = Prelude._*>_

  infixr 1 _<=<_
  _<=<_ : (b -> m c) -> (a -> m b) -> a -> m c
  _<=<_ f g x = g x >>= f

  infixr 1 _>=>_
  _>=>_ : (a -> m b) -> (b -> m c) -> a -> m c
  _>=>_ = Prelude.flip _<=<_

  join : m (m a) -> m a
  join = _>>= Prelude.id

  ap : m (a -> b) -> m a -> m b
  ap mf mx = do
    f <- mf
    x <- mx
    return (f x)

  liftM : (a -> b) -> m a -> m b
  liftM f mx = do
    x <- mx
    return (f x)

open Monad {{...}} public

data Id (a : Set) : Set where
  anId : a -> Id a

instance
  Monad-Id : Monad Id
  Monad-Id ._>>=_ (anId x) k = k x
  Monad-Id .return = anId
  Monad-Id .Applicative-super .pure = return
  Monad-Id .Applicative-super ._<*>_ = ap
  Monad-Id .Applicative-super .Functor-super .map = liftM
