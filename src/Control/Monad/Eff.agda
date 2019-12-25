{-# OPTIONS --type-in-type #-}

module Control.Monad.Eff where

-- Eff Fs is just the free monad obtained from a disjoint union of Fs.

import Control.Monad.Free as Free
open Free using (Free; Free:; Monad:Free)
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

lift : forall {F Fs} {{_ : Member F Fs}} -> F ~> Eff Fs
lift = Free.lift <<< inj

interpret : forall {M Fs} {{_ : Monad Sets M}}
  -> (Union Fs ~> M) -> Eff Fs ~> M
interpret = Free.interpret

-- Helper to handle an effect or relay it.

open import Data.Function

handleRelay : forall {F Fs X Y}
  -> (X -> Eff Fs Y)
  -> (F X -> Eff Fs Y)
  -> Union (F :: Fs) X
  -> Eff Fs Y
handleRelay loop h (left x) = h x
handleRelay loop h (right u) = extend loop (Free.lift u)

-- Eff [] X and X are isomorphic. This means that Eff [] X describes a pure
-- computation.

run : forall {X} -> Eff [] X -> X
run eff = interpret (\ ()) eff
  where instance _ = Monad:id Sets
