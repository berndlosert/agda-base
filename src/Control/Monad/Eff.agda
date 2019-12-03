{-# OPTIONS --type-in-type #-}

module Control.Monad.Eff where

-- Eff Fs is just the free monad obtained from a disjoint union of Fs.

open import Control.Monad.Free
open import Data.Functor.Union
open import Data.List.Base

Eff : List (Set -> Set) -> Set -> Set
Eff Fs X = Free (Union Fs) X

-- send is the analog of Free.lift for Eff.

open import Control.Category
open import Control.Monad
open import Data.Functor

send : forall {F Fs} {{_ : Member F Fs}} -> F ~> Eff Fs
send = lift <<< inj

-- Eff Fs is a monad whenever Union Fs is a functor.

instance
  Monad:Eff : forall {Fs}
    -> {{_ : Endofunctor Sets (Union Fs)}}
    -> Monad Sets (Eff Fs)
  Monad:Eff {Fs} = Monad:Free {Union Fs}

-- Helper to handle an effect or relay it.

open import Data.Either
open import Data.Function

handle-relay : forall {F Fs X Y}
  -> {{_ : Endofunctor Sets (Union Fs)}}
  -> Union (F :: Fs) X
  -> (X -> Eff Fs Y)
  -> (F X -> Eff Fs Y)
  -> Eff Fs Y
handle-relay (left x) loop h = h x
handle-relay {F} {Fs} (right u) loop h = extend loop (lift u)

-- Eff [] X and X are isomorphic. This means that Eff [] X describes a pure
-- computation.

run : forall {X} -> Eff [] X -> X
run eff = eff {{Monad:id Sets}} \ ()
