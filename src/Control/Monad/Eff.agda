{-# OPTIONS --type-in-type #-}

module Control.Monad.Eff where

open import Prelude
  hiding (fold)

open import Control.Monad.Free as Free
  using (Free; aFree; monadFree)

Effect : Set
Effect = Set -> Set

Effects = List Effect

Union : Effects -> Effect
Union [] _ = Void
Union (F :: Fs) A = Either (F A) (Union Fs A)

record Member (F : Effect) (Fs : Effects) : Set where
  field
    inj : F ~> Union Fs
    prj : Union Fs ~> Maybe ∘ F

open Member {{...}}

instance
  memberSingleton : ∀ {F} -> Member F [ F ]
  memberSingleton .inj = left
  memberSingleton .prj = leftToMaybe

abstract
  Eff : Effects -> Effect
  Eff Fs A = Free (Union Fs) A

  anEff : ∀ {Fs A}
    -> (∀ {M} {{_ : Monad M}} -> (Union Fs ~> M) -> M A)
    -> Eff Fs A
  anEff eff = aFree eff

  lift : ∀ {Fs} -> Union Fs ~> Eff Fs
  lift = Free.lift

  interpret : ∀ {M Fs} {{_ : Monad M}}
    -> (Union Fs ~> M) -> Eff Fs ~> M
  interpret = Free.interpret

  -- “Sends” an effect, which should be a value defined as part of an effect
  -- algebra, to an effectful computation. This is used to connect the definition
  -- of an effect to the 'Eff' monad so that it can be used and handled.

  send : ∀ {F Fs} {{_ : Member F Fs}} -> F ~> Eff Fs
  send = Free.lift ∘ inj

  -- A fold operation for Eff. This is handleRelay from freer-simple.y

  fold : ∀ {F Fs A Y}
    -> (A -> Eff Fs Y)
    -> (∀ {A} -> (A -> Eff Fs Y) -> F A -> Eff Fs Y)
    -> Eff (F :: Fs) A
    -> Eff Fs Y
  fold {F} {Fs} {_} {Y} ret ext = Free.fold ret ext'
    where
      ext' : ∀ {A} -> (A -> Eff Fs Y) -> sum (F :: Fs) A -> Eff Fs Y
      ext' ret (left x) = ext ret x
      ext' ret (right u) = Free.lift u >>= ret

  -- Eff [] A and A are isomorphic. This means that Eff [] A describes a pure
  -- computation.

  run : ∀ {A} -> Eff [] A -> A
  run eff = let absurd = λ () in
    runIdentity (interpret (anIdentity ∘ absurd) eff)

  -- This Monad instance is for exporting purposes only.

  instance
    monadEff : ∀ {Fs} -> Monad (Eff Fs)
    monadEff = monadFree
