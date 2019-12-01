*****************
Control.Monad.Eff
*****************
::

  {-# OPTIONS --type-in-type #-}

  module Control.Monad.Eff where

  open import Control.Category
  open import Control.Monad
  open import Control.Monad.Free
  open import Data.Monoid
  open import Data.Either
  open import Data.Function
  open import Data.Functor

  open import Data.Int
  open import Data.Maybe
  open import Data.Product
  open import Data.String
  open import Data.Void

``Eff Fs`` is just the free monad obtained from a disjoint union of ``Fs``::

  open import Data.Functor.Union
  open import Data.List

  Eff : List (Set → Set) → Set → Set
  Eff Fs X = Free (Union Fs) X
        -- = (Union Fs ⇒ M) → M X

These are the analogs of ``liftFree`` and ``interpretFree`` for ``Eff``::

  private
    variable 
      F M : Set → Set
      Fs : List (Set → Set)

  liftEff : ⦃ _ : Member F Fs ⦄ → F ⇒ Eff Fs
  liftEff = liftFree ∘ inj

  interpretEff : forall {Fs M} ⦃ _ : Monad Sets M ⦄
    → (Union Fs ⇒ M) → Eff Fs ⇒ M 
  interpretEff α = interpretFree α

Some theory
============

Typically, an operation on a set can be nullary, unary, binary, etc. In other
words, an operation on a set ``X`` has the form ``Xⁿ → X ``for some natural
number ``n`` (called the arity of the operation). We can generalize arities to
arbitrary sets, so an operation on ``X`` should be of the form ``(A → X) → X``.
Now, some operations have "parameters" (e.g. ``padRight : Int → String →
String`` takes an ``Int`` parameter). To account for these kinds of operations,
the general type of an operation on a set ``X`` has the form ``P → (A → X) →
X``.

A *signature* specifies a collection of operation symbols together with their parameters and arities. For example, the ``Reader R`` signature consists of only one operation symbol ``ask`` that has an ``R`` parameter and whose arity is ``Void``.

An *algebra* for the ``Reader R`` signature consists of a set ``X`` together with an "implementation" of ``ask``:

.. code-block:: agda

  ask : R → (Void → X) → X
  
Note that ``(Void → X) → X`` is isomorphic to ``Unit → X``, which is turn is isomorphic to ``X``. Thus, the implementation of ``ask`` can have the type::

.. code-block:: agda

  ask : R → X

We can represent the ``Reader R`` signature as a type class::

  record Reader (R X : Set) : Set where
    field
      ask : R → X

Hmm...

.. code-block:: agda

  instance
    Functor:Reader : {R : Set} → Endofunctor Sets (Reader R)
    Functor:Reader .map f (Ask k) = Ask (k >>> f)

  ask : forall {R Fs} ⦃ _ : Member (Reader R) Fs ⦄ → Eff Fs R
  ask = liftEff (Ask id)

  {-

  Consider a computation of type 

    Eff (F :: Fs) X

  We can handle F with a generator

    generator: X → Eff Fs X1

  and an algebra

    alg : F (Eff Fs X1) → Eff Fs X1

  While handling F1, the F2 operations are untouched and forwarded to the
  resulting computation. Here, the forwarding interpreter that achieves this is

    fwd : Union Fs (Eff Fs X1) → Eff Fs X1

  This is all combined into the handle function

    handle : Eff (F :: Fs) X → Eff Fs X1 
    handle = foldFree' gen (alg V fwd)

    where
      alg V fwd : F (Eff Fs X1) + Union Fs (Eff Fs X1) → Eff Fs X1 
                : Union (F :: Fs) (Eff Fs X1) → Eff Fs X1
  -}

  addGet : forall {Fs} ⦃ _ : Endofunctor Sets (Union Fs)  ⦄
    → ⦃ _ : Member (Reader Int) Fs ⦄ → Int → Eff Fs Int
  addGet {Fs} x = let _>>=_ = _>>=_ {Eff Fs} in
    do
      i <- ask
      return (i + x)

  runReader : forall {R Fs} → R → Eff (Reader R :: Fs) ⇒ Eff Fs
  runReader r eff t = eff \ where
    (left (Ask k)) → return (k r)
    (right u) → t u

  test1 : Int
  test1 = run $ runReader 10 $ addGet 1

  data Writer (W K : Set) : Set where
    put : W → K → Writer W K

  instance
    Functor:Writer : {W : Set} → Endofunctor Sets (Writer W)
    Functor:Writer .map f (put w k) = put w (f k)

  tell : forall {W Fs} ⦃ _ : Member (Writer W) Fs ⦄
    → W → Eff Fs Unit
  tell w = liftEff (put w tt)

  runWriter : forall {W X Fs}
    → ⦃ _ : Monoid W ⦄
    → ⦃ _ : Endofunctor Sets (Union Fs) ⦄
    → Eff (Writer W :: Fs) X → Eff Fs (X * W)
  runWriter = handle (_, mempty) (\ eff alpha → eff \ where
      (left (put w y)) → return y
      (right u) → alpha u
    )

  writerProg : forall {Fs} ⦃ _ : Endofunctor Sets (Union Fs) ⦄
    → ⦃ _ : Member (Writer String) Fs ⦄ → Eff Fs Int
  writerProg {Fs} = let _>>=_ = _>>=_ {Eff Fs} in
    do
      _ <- tell "hi "
      _ <- tell "there "
      return 10

  test2 : Int * String
  test2 = run $ runWriter $ writerProg

  --test3 : test2 === (10 , "hi there ")
  --test3 = refl

A term of type ``Eff [] X`` cannot produce a computational effect. This is evidenced by the operation ``run`` below::

  private variable X : Set

  run : Eff [] X → X
  run eff = eff ⦃ Monad:id Sets ⦄ absurd