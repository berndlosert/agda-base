open import Prelude

open import Data.Enum
open import Data.Foldable
open import System.IO

variable
  a b : Set
  t : Set -> Set

data Strict (a : Set) : Set where
  asStrict' : a -> Strict a

asStrict : a -> Strict a
asStrict x = x seq (asStrict x)

strict : (a -> b) -> Strict a -> b
strict f (asStrict' x) = f $! x

foldl' : {{Foldable t}} -> (Strict b -> a -> b) -> b -> t a -> b
foldl' {t} {b} {a} step init xs = foldr step' id xs init
  where
    step' : a -> (b -> b) -> b -> b
    step' x k acc = k (step (asStrict acc) x)

_+'_ : Strict Nat -> Nat -> Nat
(asStrict' x) +' y = x + y

main : IO Unit
main = do
  print $ foldl' _+'_ (the Nat 0) $ enumFromTo 0 10_000_000