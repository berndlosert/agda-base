module Control.Monad.Free.Scoped where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    c f g : Type -> Type

-------------------------------------------------------------------------------
-- Free
-------------------------------------------------------------------------------

-- From "Structured Handling of Scoped Effects"
data Free (f g : Type -> Type) (a : Type) : Type where
 return : a -> Free f g a
 call : f (Free f g a) -> Free f g a
 enter : g (Free f g (Free f g a)) -> Free f g a

instance
  mutual
    Functor-Free : {{Functor f}} -> {{Functor g}} -> Functor (Free f g)
    Functor-Free .map = liftM

    Applicative-Free : {{Functor f}} -> {{Functor g}}  -> Applicative (Free f g)
    Applicative-Free ._<*>_ = ap
    Applicative-Free .pure = return

    Monad-Free : {{Functor f}} -> {{Functor g}} -> Monad (Free f g)
    Monad-Free ._>>=_ (return x) k = k x
    Monad-Free ._>>=_ (call op) k = call (map (_>>= k) op)
    Monad-Free ._>>=_ (enter sc) k = enter (map (map (_>>= k)) sc)

-------------------------------------------------------------------------------
-- EndoAlg
-------------------------------------------------------------------------------

record EndoAlg (f g c : Type -> Type) : Type where
  constructor anEndoAlg
  field
    returnE : a -> c a
    callE : f (c a) -> c a
    enterE : g (c (c a)) -> c a

open EndoAlg public

hcata : {{Functor f}} -> {{Functor g}} -> EndoAlg f g c -> Free f g a -> c a
hcata ealg (return x) = returnE ealg x
hcata ealg (call op) = (callE ealg <<< map (hcata ealg)) op
hcata ealg (enter sc) = (enterE ealg <<< map (hcata ealg <<< map (hcata ealg))) sc

-------------------------------------------------------------------------------
-- BaseAlg
-------------------------------------------------------------------------------

record BaseAlg (f g c : Type -> Type) (a : Type) : Type where
  constructor anBaseAlg
  field
    callB : f a -> a
    enterB : g (c a) -> a

open BaseAlg public

handle : {{Functor f}} -> {{Functor g}}
  -> EndoAlg f g c -> BaseAlg f g c b -> (a -> b) -> Free f g a -> b
handle ealg balg gen (return x) = gen x
handle ealg balg gen (call op) = (callB balg <<< map (handle ealg balg gen)) op
handle ealg balg gen (enter sc) =
  (enterB balg <<< map (hcata ealg <<< map (handle ealg balg gen))) sc
