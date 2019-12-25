{-# OPTIONS --type-in-type #-}

module Control.Monad.Free where

-- Let C be a category and let F : ob C -> ob C. A free monad on F is a monad
-- Free F on C equipped with a natural transformation lift : F ~> Free F
-- satisfying the following universal property: for any monad M on C and
-- natural transformation t : F ~> M, there is a unique monad morphism
-- interpret t : Free F ~> M with the property that t = interpret t <<< lift.
-- When C = Sets, we define Free F, lift and interpret as follows:

open import Control.Category
open import Control.Monad
open import Data.Functor

record Free (F : Set -> Set) (X : Set) : Set where
  constructor Free:
  field
    run : forall {M} {{_ : Monad Sets M}} -> (F ~> M) -> M X

open Free

lift : forall {F} -> F ~> Free F
lift x = Free: \ t -> t x

interpret : forall {F M} {{_ : Monad Sets M}} -> (F ~> M) -> Free F ~> M
interpret t free = run free t

-- This is the left inverse (retract) of lift.

lower : forall {M} {{_ : Monad Sets M}} -> Free M ~> M
lower = interpret id

-- Free F is a monad whenever F is a functor.

instance
  Monad:Free : forall {F} -> Monad Sets (Free F)
  Monad:Free .return x = Free: \ _ -> return x
  Monad:Free .extend f m = Free: \ t -> 
    join (map (interpret t <<< f) (interpret t m))

-- Free forms a functor on the category Sets ^ Sets whose map operation is:

hoist : forall {F G} -> (F ~> G) -> Free F ~> Free G
hoist t free = run free (lift <<< t)

-- Free also forms a monad on Sets ^ Sets. The return operation of this monad
-- is lift; the extend operation is defined below:

flatMap : forall {F G}
  -> (F ~> Free G) -> Free F ~> Free G
flatMap = interpret

-- Free is a free construction. It is basically the left-adjoint of the
-- would-be forgetful functor U that forgets the monad structure of a functor.
-- The right adjunct of this adjunction is basically interpret. The left
-- adjunct is given below.

uninterpret : forall {F M} -> (Free F ~> M) -> F ~> M
uninterpret t x = t (lift x)

-- When F is a functor, Free F X is an F-algebra for any type X. The operation
-- of this algebra is:

impure : forall {F X} -> F (Free F X) -> Free F X
impure op = join (lift op)
