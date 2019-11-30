{-# OPTIONS --type-in-type #-}

module Control.Monad.Free where

-- Let C be a category and let F : ob C → ob C be a functor. A free monad on F 
-- is a monad Free F : ob C → ob C equipped with a natural transformation 
-- liftFree : F ⇒ Free F satisfying the following universal property: for any
-- monad M : ob C → ob C and natural transformation alpha : F ⇒ M, there is a 
-- unique monad morphism interpretFree alpha : Free F ⇒ M with the property 
-- that l = liftFree >>> interpretFree. When C = Sets, we define Free F, 
-- liftFree and interpretFree as follows:

open import Control.Category
open import Control.Monad
open import Data.Functor

-- This is the final encoding of Free. The other encodings of Free cause
-- problems either with the positivity checker or with the termination checker
-- when defining foldFree.
Free : (Set → Set) → Set → Set
Free F X = forall {M} {{_ : Monad Sets M}} → (F ⇒ M) → M X

liftFree : forall {F} → F ⇒ Free F
liftFree x alpha = alpha x

interpretFree : forall {F M} {{_ : Monad Sets M}}
  → (F ⇒ M) → Free F ⇒ M 
interpretFree alpha free = free alpha

-- This is the left inverse of liftFree.
retractFree : forall {M} {{_ : Monad Sets M}} → Free M ⇒ M
retractFree = interpretFree id 

instance 
  -- Proof that Free F is a functor. Note that this doesn't require F to be
  -- a functor. However, this is not a free construction.
  Functor:Free : forall {F} → Endofunctor Sets (Free F)
  Functor:Free .map f free alpha = map f (free alpha)

-- Free F is a monad whenever F is a functor. We don't make this an instance
-- because Agda get's confused sometimes when it tries to figure out the
-- instance to use for Endofunctor Sets F.
Monad:Free : forall {F} {{_ : Endofunctor Sets F}} → Monad Sets (Free F)
Monad:Free .join free alpha = join (map (\ f → f alpha) (free alpha))
Monad:Free .return x _ = return x

-- Free is a free construction, i.e. it is basically the left-adjoint of the
-- would-be forgetful functor U that forgets the monad structure of a functor.
-- The right adjunct of this adjunction is basically interpretFree. The left
-- adjunct is given below. 
uninterpretFree : forall {F M} → (Free F ⇒ M) → (F ⇒ M)
uninterpretFree alpha x = alpha (liftFree x)

-- When F is a functor, (Free F X , algFree) is an F-algebra.
algFree : forall {F X} {{_ : Endofunctor Sets F}} → F (Free F X) → Free F X 
algFree = liftFree >>> join
  where instance _ = Monad:Free

-- A different version of interpretFree that takes a generator gen : X → Y and
-- and M-algebra alg : M Y → Y and produces a fold of type Free M X → Y. This
-- fold is based on the Church encoding of Free.
foldFree : forall {M X Y} {{_ : Monad Sets M}}
  → (X → Y) → (M Y → Y) → Free M X → Y
foldFree gen alg free = alg (map gen (retractFree free))
