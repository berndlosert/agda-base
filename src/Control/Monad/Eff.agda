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
Union (F :: Fs) A = (F + Union Fs) A

private
  variable
    A B : Set
    F M : Effect
    Fs : Effects

record Member (F : Effect) (Fs : Effects) : Set where
  field
    inj : F ~> Union Fs
    prj : Union Fs ~> Maybe ∘ F

open Member {{...}}

instance
  memberSingleton : Member F (F :: Fs)
  memberSingleton .inj = Left
  memberSingleton .prj = leftToMaybe

abstract
  Eff : Effects -> Effect
  Eff = Free ∘ Union

  anEff : (forall {M} {{_ : Monad M}} -> (Union Fs ~> M) -> M A) -> Eff Fs A
  anEff eff = aFree eff

  lift : Union Fs ~> Eff Fs
  lift = Free.lift

  interpret : {{_ : Monad M}} -> (Union Fs ~> M) -> Eff Fs ~> M
  interpret = Free.interpret

  -- “Sends” an effect, which should be a value defined as part of an effect
  -- algebra, to an effectful computation. This is used to connect the definition
  -- of an effect to the 'Eff' monad so that it can be used and handled.
  send : {{_ : Member F Fs}} -> F ~> Eff Fs
  send = Free.lift ∘ inj

  -- A fold operation for Eff. This is handleRelay from freer-simple.y

  fold : forall {F Fs A B}
    -> (A -> Eff Fs B)
    -> (forall {A} -> (A -> Eff Fs B) -> F A -> Eff Fs B)
    -> Eff (F :: Fs) A
    -> Eff Fs B
  fold {F} {Fs} {_} {B} ret ext = Free.fold ret ext'
    where
      ext' : forall {A} -> (A -> Eff Fs B) -> Union (F :: Fs) A -> Eff Fs B
      ext' ret (Left x) = ext ret x
      ext' ret (Right u) = Free.lift u >>= ret

  -- Eff [] A and A are isomorphic. This means that Eff [] A describes a pure
  -- computation.
  run : Eff [] A -> A
  run = runIdentity ∘ (interpret λ ())

  instance
    monadEff : Monad (Eff Fs)
    monadEff = monadFree
