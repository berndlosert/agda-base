module Control.Monad.Free.Reader where

open import Prelude

open import Control.Monad.Eff as Eff
  using (Effect; Union; Member; Eff)

Reader : Set -> Effect
Reader r a = r -> a

ask : forall {r fs} {{_ : Member (Reader r) fs}} -> Eff fs r
ask = Eff.send id

run : forall {r fs a} -> r -> Eff (Reader r :: fs) a -> Eff fs a
run r = Eff.interpret λ where
  (Left k) -> return (k r)
  (Right u) -> Eff.lift u
