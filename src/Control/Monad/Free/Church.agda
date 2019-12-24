{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Church where

-- Free is the "Church" encoding of the traditional definition of Free: 
--
--   data Free (F : Set -> Set) (X : Set) : Set where
--     pure : X -> Free F X
--     impure : F (Free F X) -> Free F X
--
-- The above definition won't compile in Agda because it doesn't pass the
-- strict positivity checker.    

record Free (F : Set -> Set) (X : Set) : Set where
  constructor Free:
  field
    run : forall {Y} -> (X -> Y) -> (F Y -> Y) -> Y

open Free

-- Free F is a functor.

open import Control.Category
open import Data.Functor

instance
  Functor:Free : forall {F} -> Endofunctor Sets (Free F)
  Functor:Free .map f freer .run gen alg = run freer (gen <<< f) alg

-- Free F is a monad. Note that it doesn't require F to be a functor.

open import Control.Monad

Monad:Free : forall {F} -> Monad Sets (Free F)
Monad:Free {F} = Triple: ext ret 
  where
    ext : forall {X Z} -> (X -> Free F Z) -> Free F X -> Free F Z
    ext f freer .run gen alg = run freer (\ x -> run (f x) gen alg) alg

    ret : forall {X} -> X -> Free F X
    ret x .run gen alg = gen x

-- The lift and lower operations for the Free construction.

lift : forall {F} {{_ : Endofunctor Sets F}} -> F ~> Free F
lift x .run gen alg = alg (map gen x)

lower : forall {M} {{_ : Monad Sets M}} -> Free M ~> M 
lower freer = run freer return join

-- Free is the left adjoint of the forgetful functor U that forgets both the
-- monad and functor structures. The left/right adjuncts of this adjunction
-- are:

uninterpret : forall {F M} {{_ : Endofunctor Sets F}}
  -> (Free F ~> M) -> F ~> M
uninterpret t x = t (lift x)

interpret : forall {F M} {{_ : Monad Sets M}} -> (F ~> M) -> Free F ~> M
interpret t freer = run freer return (t >>> join)
