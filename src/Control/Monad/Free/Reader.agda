{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Reader where

open import Prelude

open import Control.Monad.Eff as Eff
  using (Effect; Union; Member; Eff)

Reader : Set -> Effect
Reader R A = R -> A

ask : forall {R Fs} {{_ : Member (Reader R) Fs}} -> Eff Fs R
ask = Eff.send id

run : forall {R Fs X} -> R -> Eff (Reader R :: Fs) X -> Eff Fs X
run {R} {Fs} r eff = Eff.interpret t eff
  where
    t : Union (Reader R :: Fs) ~> Eff Fs
    t (left k) = return (k r)
    t (right u) = Eff.lift u
