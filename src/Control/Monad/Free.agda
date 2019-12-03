{-# OPTIONS --type-in-type #-}

module Control.Monad.Free where

-- Let C be a category and let F be an endofunctor on C. A free monad on F is a
-- monad Free F on C equipped with a natural transformation lift : F ~> Free F
-- satisfying the following universal property: for any monad M on C and
-- natural transformation t : F ~> M, there is a unique monad morphism foldMap
-- t : Free F ~> M with the property that t = foldMap t <<< lift. When C =
-- Sets, we define Free F, lift and foldMap as follows:

-- (N.B. We give the final encoding of Free. The other encodings of Free
-- cause problems either with the positivity checker or with the termination
-- checker when defining foldMap.)

open import Control.Category
open import Control.Monad
open import Data.Functor

Free : (Set -> Set) -> Set -> Set
Free F X = forall {M} {{_ : Monad Sets M}} -> (F ~> M) -> M X

lift : forall {F} -> F ~> Free F
lift x t = t x

foldMap : forall {F M} {{_ : Monad Sets M}} -> (F ~> M) -> Free F ~> M
foldMap t free = free t

-- This is the left inverse (retract) of lift.

fold : forall {M} {{_ : Monad Sets M}} -> Free M ~> M
fold = foldMap id

-- The foldr analog for Free. Notice the similarity with the version from Foldable.

open import Control.Monad.Codensity

foldr : forall {F G} {{_ : Endofunctor Sets F}}
  -> (F <<< G ~> G) -> (id ~> G) -> Free F ~> G
foldr {F} {G} jn ret free = foldMap {{Monad:Codensity {G}}} bnd free ret
  where
    bnd : F ~> Codensity G
    bnd x k = jn (map k x)

-- Here is proof that Free F is a functor. Note that this doesn't require F to
-- be a functor. However, this is not a free construction.

instance
  Functor:Free : forall {F} -> Endofunctor Sets (Free F)
  Functor:Free .map f free t = map f (free t)

-- Free F is a monad whenever F is a functor. We don't make this an instance
-- because Agda gets confused sometimes when it tries to figure out the
-- instance to use for Endofunctor Sets F.

Monad:Free : forall {F} {{_ : Endofunctor Sets F}} -> Monad Sets (Free F)
Monad:Free .join free t = join (map (\ f -> f t) (free t))
Monad:Free .return x _ = return x

-- Free is a free construction. It is basically the left-adjoint of the
-- would-be forgetful functor U that forgets the monad structure of a functor.
-- The right adjunct of this adjunction is basically foldMap. The left
-- adjunct is given below.

leftAdjunct : forall {F M} -> (Free F ~> M) -> F ~> M
leftAdjunct t x = t (lift x)

-- When F is a functor, (Free F X , freeAlg) is an F-algebra for any type X.

freeAlg : forall {F X} {{_ : Endofunctor Sets F}}
  -> F (Free F X) -> Free F X
freeAlg = join <<< lift
  where instance _ = Monad:Free
