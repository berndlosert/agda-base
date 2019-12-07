{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer where

-- Writer W X models computations of type X that store a value of type W. We
-- call such computations Writer computations.

open import Data.Product

Writer : Set -> Set -> Set
Writer W X = X * W

-- Writer W is a functor. The proof is provided by Endofunctor:Product.

open import Data.Functor

-- The tell function will produce a Writer computation that just stores the
-- given value.

open import Control.Monad.Eff
open import Data.Unit

tell : forall {W Fs} {{_ : Member (Writer W) Fs}} -> W -> Eff Fs Unit
tell w = liftEff (tt , w)

-- Simple handler of Writer W effects.

open import Control.Category
open import Control.Monad
open import Control.Monad.Free
open import Data.Monoid

runWriter : forall {W Fs X}
  -> {{_ : Monoid W}}
  -> {{_ : Endofunctor Sets (Union Fs)}}
  -> Eff (Writer W :: Fs) X -> Eff Fs (X * W)
runWriter {W} {Fs} eff = runEff eff trans 
  where
    ret : forall {Y} -> Y -> Y * W
    ret = (_, mempty)

    ext : forall {Y Z}
      -> (Y -> Eff Fs (Z * W))
      -> Eff Fs (Y * W) -> Eff Fs (Z * W)
    ext f = extend (f <<< fst)

    instance
      _ : Monad Sets (Eff Fs <<< (_* W))
      _ = Triple: ext (return <<< ret)

    trans : forall {Y} -> Union (Writer W :: Fs) Y -> Eff Fs (Y * W) 
    trans (left (y , w)) = return (y , w)
    trans (right u) = map ret (liftFree u)

-- If W is a monoid, then Writer W is a monad. The return function in this case
-- produces a Writer computation that stores mempty. The bind operation
-- essentially does function application while combining the stored values
-- using the monoid operation.

--instance
--  Monad:Writer : forall {W} {{_ : Monoid W}} -> Monad Sets (Writer W)
--  Monad:Writer = record {
--      instance:Functor = Functor:Writer;
--      join = \ { ((x , w) , w') -> (x , w <> w') };
--      return = \ x -> (x , mempty)
--    }
