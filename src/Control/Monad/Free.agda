{-# OPTIONS --type-in-type #-}

module Control.Monad.Free where

-- Let C be a category and let F be an endofunctor on C. A free monad on F is a
-- monad Free F on C equipped with a natural transformation lift : F ~> Free F
-- satisfying the following universal property: for any monad M on C and
-- natural transformation t : F ~> M, there is a unique monad morphism foldMap
-- t : Free F ~> M with the property that t = foldMap t <<< lift. When C =
-- Sets, we define Free F, lift and foldMap as follows:

open import Control.Category
open import Control.Monad hiding (extend)
open import Data.Functor

record Free (F : Set -> Set) (X : Set) : Set where
  constructor Free:
  field
    run : forall {M} {{_ : Monad Sets M}} -> (F ~> M) -> M X

open Free

lift : forall {F} -> F ~> Free F
lift x = Free: \ t -> t x

foldMap : forall {F M} {{_ : Monad Sets M}} -> (F ~> M) -> Free F ~> M
foldMap t free = run free t

-- This is the left inverse (retract) of lift.

fold : forall {M} {{_ : Monad Sets M}} -> Free M ~> M
fold = foldMap id

-- The foldr analog for Free. Notice the similarity with the version from
-- Foldable.

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
  Functor:Free .map f free = Free: \ t -> map f (run free t)

-- Free F is a monad whenever F is a functor.

instance
  Monad:Free : forall {F} {{_ : Endofunctor Sets F}} -> Monad Sets (Free F)
  Monad:Free .join free = Free: \ t -> join (map (\ f -> run f t) (run free t))
  Monad:Free .return x = Free: \ _ -> return x

-- Free forms a functor on the category Sets ^ Sets whose map operation is:

hoist : forall {F G} {{_ : Endofunctor Sets G}}
  -> (F ~> G) -> Free F ~> Free G
hoist t free = run free (lift <<< t)

-- Free also forms a monad on Sets ^ Sets. The return operation of this monad
-- is lift; the extend operation is defined below:

extend : forall {F G} {{_ : Endofunctor Sets G}}
  -> (F ~> Free G) -> Free F ~> Free G
extend = foldMap

-- Free is a free construction. It is basically the left-adjoint of the
-- would-be forgetful functor U that forgets the monad structure of a functor.
-- The right adjunct of this adjunction is basically foldMap. The left
-- adjunct is given below.

uninterpret : forall {F M} -> (Free F ~> M) -> F ~> M
uninterpret t x = t (lift x)

-- When F is a functor, Free F X is an F-algebra for any type X. The operation
-- of this algebra is:

impure : forall {F X} {{_ : Endofunctor Sets F}}
  -> F (Free F X) -> Free F X
impure = join <<< lift
