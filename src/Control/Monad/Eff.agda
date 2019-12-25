{-# OPTIONS --type-in-type #-}

module Control.Monad.Eff where

-- Eff Fs is just the free monad obtained from a disjoint union of Fs.

import Control.Monad.Free as Free
open Free using (Free; Free:; Monad:Free)
open import Data.Functor.Union

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

-- The Eff versions of lift and interpret.

open import Control.Category
open import Control.Monad
open import Data.Functor

lift : forall {Fs} -> Union Fs ~> Eff Fs
lift = Free.lift

interpret : forall {M Fs} {{_ : Monad Sets M}}
  -> (Union Fs ~> M) -> Eff Fs ~> M
interpret = Free.interpret

-- “Sends” an effect, which should be a value defined as part of an effect
-- algebra, to an effectful computation. This is used to connect the definition
-- of an effect to the 'Eff' monad so that it can be used and handled.

send : forall {F Fs} {{_ : Member F Fs}} -> F ~> Eff Fs
send = Free.lift <<< inj

-- A fold operation for Eff. This is handleRelay from freer-simple.y

open import Data.Function

fold : forall {F Fs X Y}
  -> (X -> Eff Fs Y)
  -> (forall {X} -> (X -> Eff Fs Y) -> F X -> Eff Fs Y)
  -> Eff (F :: Fs) X
  -> Eff Fs Y
fold {F} {Fs} {_} {Y} ret ext = Free.fold ret ext'
  where
    ext' : forall {X} -> (X -> Eff Fs Y) -> Union (F :: Fs) X -> Eff Fs Y
    ext' ret (left x) = ext ret x 
    ext' ret (right u) = extend ret (Free.lift u)

-- Eff [] X and X are isomorphic. This means that Eff [] X describes a pure
-- computation.

run : forall {X} -> Eff [] X -> X
run eff = interpret (\ ()) eff
  where instance _ = Monad:id Sets

-- This Monad instance is for exporting purposes only.

instance
  Monad:Eff : forall {Fs} -> Monad Sets (Eff Fs)
  Monad:Eff = Monad:Free 
