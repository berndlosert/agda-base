{-# OPTIONS --type-in-type #-}

module Control.Monad.Free where

-- Let C be a category and let F be an endofunctor on C. A free monad on F is a
-- monad Free F on C equipped with a natural transformation liftFree : F ~>
-- Free F satisfying the following universal property: for any monad M on C and
-- natural transformation t : F ~> M, there is a unique monad morphism foldFree
-- t : Free F ~> M with the property that t = foldFree t <<< liftFree. When C =
-- Sets, we define Free F, liftFree and foldFree as follows:

-- (N.B. We give the final encoding of Free. The other encodings of Free
-- cause problems either with the positivity checker or with the termination
-- checker when defining foldFree.)

open import Control.Category
open import Control.Monad
open import Data.Functor

record Free (F : Set -> Set) (X : Set) : Set where
  constructor Free:
  field
    runFree : forall {M} {{_ : Monad Sets M}} -> (F ~> M) -> M X

open Free public

liftFree : forall {F} -> F ~> Free F
liftFree x = Free: \ t -> t x

foldFree : forall {F M} {{_ : Monad Sets M}} -> (F ~> M) -> Free F ~> M
foldFree t free = runFree free t

-- This is the left inverse (retract) of liftFree.

retractFree : forall {M} {{_ : Monad Sets M}} -> Free M ~> M
retractFree = foldFree id

-- The foldr analog for Free. Notice the similarity with the version from
-- Foldable.

open import Control.Monad.Codensity

foldrFree : forall {F G} {{_ : Endofunctor Sets F}}
  -> (F <<< G ~> G) -> (id ~> G) -> Free F ~> G
foldrFree {F} {G} jn ret free = foldFree {{Monad:Codensity {G}}} bnd free ret
  where
    bnd : F ~> Codensity G
    bnd x k = jn (map k x)

-- Here is proof that Free F is a functor. Note that this doesn't require F to
-- be a functor. However, this is not a free construction.

instance
  Functor:Free : forall {F} -> Endofunctor Sets (Free F)
  Functor:Free .map f free = Free: \ t -> map f (runFree free t)

-- Free F is a monad whenever F is a functor.

instance
  Monad:Free : forall {F} {{_ : Endofunctor Sets F}} -> Monad Sets (Free F)
  Monad:Free .join free = Free: \ t -> join (map (\ f -> runFree f t) (runFree free t))
  Monad:Free .return x = Free: \ _ -> return x

-- Free itself is a monad on the functor category Sets ^ Sets. The return
-- operation of this monad is liftFree; the extend operation is given below.
-- This operation is essential in constructing handlers of algebraic effects.

extendFree : forall {F G} {{_ : Endofunctor Sets G}}
  -> (F ~> G) -> Free F ~> Free G
extendFree t free = runFree free (liftFree <<< t)

-- The handle function allows us to translate a Free F X computation into a Y,
-- given a function X -> Y and a transformation F ~> id.

handleFree : forall {X Y : Set} {F}
  -> (X -> Y)
  -> (F ~> id) 
  -> Free F X -> Y
handleFree f t free = f (runFree (extendFree t free) id)
  where instance _ = Monad:id Sets
  
-- Free is a free construction. It is basically the left-adjoint of the
-- would-be forgetful functor U that forgets the monad structure of a functor.
-- The right adjunct of this adjunction is basically foldFree. The left
-- adjunct is given below.

uninterpretFree : forall {F M} -> (Free F ~> M) -> F ~> M
uninterpretFree t x = t (liftFree x)

-- When F is a functor, (Free F X , impure) is an F-algebra for any type X.

impure : forall {F X} {{_ : Endofunctor Sets F}}
  -> F (Free F X) -> Free F X
impure = join <<< liftFree
