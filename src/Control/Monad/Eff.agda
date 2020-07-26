module Control.Monad.Eff where

open import Prelude
  hiding (fold)

open import Control.Monad.Free as Free
  using (Free; Free:; monadFree)

Effect : Set
Effect = Set -> Set

Effects = List Effect

Union : Effects -> Effect
Union [] _ = Void
Union (f :: fs) a = (f + Union fs) a

private
  variable
    a b : Set
    f m : Effect
    fs : Effects

record Member (f : Effect) (fs : Effects) : Set where
  field
    inj : f ~> Union fs
    prj : Union fs ~> Maybe ∘ f

open Member {{...}}

instance
  memberSingleton : Member f (f :: fs)
  memberSingleton .inj = Left
  memberSingleton .prj = leftToMaybe

abstract
  Eff : Effects -> Effect
  Eff = Free ∘ Union

  Eff: : forall {a} -> (forall {m} {{_ : Monad m}} -> (Union fs ~> m) -> m a)
    -> Eff fs a
  Eff: eff = Free: eff

  lift : Union fs ~> Eff fs
  lift = Free.lift

  interpret : {{_ : Monad m}} -> (Union fs ~> m) -> Eff fs ~> m
  interpret = Free.interpret

  -- “Sends” an effect, which should be a value defined as part of an effect
  -- algebra, to an effectful computation. This is used to connect the definition
  -- of an effect to the 'Eff' monad so that it can be used and handled.
  send : {{_ : Member f fs}} -> f ~> Eff fs
  send = Free.lift ∘ inj

  -- a fold operation for Eff. This is handleRelay from freer-simple.y

  fold : forall {f fs a b}
    -> (a -> Eff fs b)
    -> (forall {a} -> (a -> Eff fs b) -> f a -> Eff fs b)
    -> Eff (f :: fs) a
    -> Eff fs b
  fold ret ext = Free.fold ret λ where
    ret' (Left x) -> ext ret' x
    ret' (Right u) -> Free.lift u >>= ret'

  -- Eff [] a and a are isomorphic. This means that Eff [] a describes a pure
  -- computation.
  run : Eff [] a -> a
  run = runIdentity ∘ (interpret λ ())

  instance
    monadEff : Monad (Eff fs)
    monadEff = monadFree
