{-# OPTIONS --type-in-type #-}

module Control.Monad.Eff where

-- Eff Fs is just the free monad obtained from a disjoint union of Fs.

open import Control.Monad.Free
open import Data.Functor.Union
open import Data.List

Eff : List (Set -> Set) -> Set -> Set
Eff Fs X = Free (Union Fs) X

-- These are the analogs of liftFree and interpretFree for Eff.

open import Control.Category
open import Control.Monad
open import Data.Functor

liftEff : forall {F Fs} {{_ : Member F Fs}} -> F ~> Eff Fs
liftEff = liftFree <<< inj

interpretEff : forall {M Fs} {{_ : Monad Sets M}}
  -> (Union Fs ~> M) -> Eff Fs ~> M
interpretEff alpha = interpretFree alpha
