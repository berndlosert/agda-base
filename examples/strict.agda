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
asStrict x = x seq (asStrict' x)

strict : (a -> b) -> Strict a -> b
strict f (asStrict' x) = f $! x

instance
  Coercible-from-Strict : Coercible (Strict a) a
  Coercible-from-Strict = coercible

  Coercible-to-Strict : Coercible a (Strict a)
  Coercible-to-Strict = coercible

_$!!_ : (Strict a -> b) -> a -> b
_$!!_ f x = f $! (coerce x)

foldl' : {{Foldable t}} -> (Strict b -> a -> b) -> b -> t a -> b
foldl' {t} {b} {a} step init xs = foldr step' id xs init
  where
    step' : a -> (b -> b) -> b -> b
    step' x k acc = k ((step $!! acc) x)

_+'_ : Strict Nat -> Nat -> Nat
x +' y = (coerce x) + y

--        Elapsed (wall clock) time (h:mm:ss or m:ss): 0:00.62
--         Maximum resident set size (kbytes): 4996
main : IO Unit
main = do
  print $ foldl' _+'_ (id {Nat} 0) $ enumFromTo 0 10_000_000