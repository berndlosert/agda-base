******************
Control.Monad.Free
******************
::

  {-# OPTIONS --type-in-type #-}

  module Control.Monad.Free where

Let ``C`` be a category and let ``F`` be an endofunctor on ``C``. A free monad
on ``F`` is a monad ``Free F`` on ``C`` equipped with a natural transformation
``liftFree : F ~> Free F`` satisfying the following universal property: for any
monad ``M`` on ``C`` and natural transformation ``α : F ~> M``, there is a
unique monad morphism ``interpretFree α : Free F ~> M`` with the property that
``α = interpretFree α ∘ liftFree``. When ``C = Sets``, we define ``Free F``,
``liftFree`` and ``interpretFree`` as follows:

(N.B. This is the final encoding of ``Free``. The other encodings of ``Free``
cause problems either with the positivity checker or with the termination
checker when defining ``interpretFree``)::

  private variable F M : Set -> Set

  open import Control.Category
  open import Control.Monad
  open import Data.Functor

  Free : (Set -> Set) -> Set -> Set
  Free F X = forall {M} {{_ : Monad Sets M}} -> (F ~> M) -> M X

  liftFree : F ~> Free F
  liftFree x α = α x

  interpretFree : {{_ : Monad Sets M}} -> (F ~> M) -> Free F ~> M 
  interpretFree α free = free α

  -- This is the left inverse of liftFree.
  retractFree : {{_ : Monad Sets M}} -> Free M ~> M
  retractFree = interpretFree id 

Here is proof that ``Free F`` is a functor. Note that this doesn't require
``F`` to be a functor. However, this is not a free construction::

  instance 
    Functor:Free : Endofunctor Sets (Free F)
    Functor:Free .map f free α = map f (free α)

``Free F`` is a monad whenever ``F`` is a functor. We don't make this an
instance because Agda get's confused sometimes when it tries to figure out the
instance to use for ``Endofunctor Sets F``::

  Monad:Free : {{_ : Endofunctor Sets F}} -> Monad Sets (Free F)
  Monad:Free .join free α = join (map (\ f -> f α) (free α))
  Monad:Free .return x _ = return x

``Free`` is a free construction. It is basically the left-adjoint of the
would-be forgetful functor ``U`` that forgets the monad structure of a functor.
The right adjunct of this adjunction is basically ``interpretFree``. The left
adjunct is given below::

  uninterpretFree : (Free F ~> M) -> (F ~> M)
  uninterpretFree α x = α (liftFree x)

When ``F`` is a functor, ``(Free F X , algFree)`` is an ``F``-algebra for any
set ``X``::

  algFree : {{_ : Endofunctor Sets F}} -> F ∘ Free F ~> Free F 
  algFree = join ∘ liftFree
    where instance _ = Monad:Free

A different version of interpretFree that takes a generator ``gen : X -> Y`` and
an ``M``-algebra ``alg : M Y -> Y`` and produces a fold of type ``Free M X ->
Y``. This fold is based on the Church encoding of ``Free``::

  private variable X Y : Set

  foldFree : {{_ : Monad Sets M}} -> (X -> Y) -> (M Y -> Y) -> Free M X -> Y
  foldFree gen alg free = alg (map gen (retractFree free))
