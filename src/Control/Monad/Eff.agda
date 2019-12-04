{-# OPTIONS --type-in-type #-}

module Control.Monad.Eff where

-- Eff Fs is just the free monad obtained from a disjoint union of Fs.

open import Control.Monad.Free
open import Data.Functor.Union public

Eff : List (Set -> Set) -> Set -> Set
Eff Fs X = Free (Union Fs) X

-- We hide the constructor Free: and instead provide a constructor Eff: for
-- creating values of type Eff Fs X.

open import Control.Category
open import Control.Monad
open import Data.Functor

Eff: : forall {Fs X}
  -> (forall {M} {{_ : Monad Sets M}} -> (Union Fs ~> M) -> M X)
  -> Eff Fs X
Eff: eff = Free: eff

-- The Eff versions of liftFree, runFree and foldFree.

open import Control.Category
open import Control.Monad
open import Data.Functor

liftEff : forall {F Fs} {{_ : Member F Fs}} -> F ~> Eff Fs
liftEff = liftFree <<< inj

runEff : forall {M Fs X} {{_ : Monad Sets M}}
  -> Eff Fs X -> (Union Fs ~> M) -> M X
runEff eff = runFree eff

foldEff : forall {M Fs} -> {{_ : Monad Sets M}}
  -> (Union Fs ~> M) -> Eff Fs ~> M
foldEff = foldFree

-- Helper to handle an effect or relay it.

open import Data.Function

handleRelay : forall {F Fs X Y}
  -> {{_ : Endofunctor Sets (Union Fs)}}
  -> Union (F :: Fs) X
  -> (X -> Eff Fs Y)
  -> (F X -> Eff Fs Y)
  -> Eff Fs Y
handleRelay (left x) loop h = h x
handleRelay {F} {Fs} (right u) loop h = extend loop (liftFree u)

-- Eff [] X and X are isomorphic. This means that Eff [] X describes a pure
-- computation.

run : forall {X} -> Eff [] X -> X
run eff = runEff eff \ ()
  where instance _ = Monad:id Sets
