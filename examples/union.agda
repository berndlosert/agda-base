open import Prelude

open import Data.Union

variable
  a b c : Set

f : Nat -> Union (Nat :: String :: Bool :: [])
f 0 = inj true
f 1 = inj ""
f 2 = inj (the Nat 0)
f _ = inj false

g : Union (Nat :: String :: Bool :: []) -> Nat
g u = case prj Nat u of \ where
  (just n) -> n
  nothing -> case prj Bool u of \ where
    (just b) -> if b then 1 else 0
    nothing -> case prj String u of \ where
      (just _) -> 1
      nothing -> case prj Nat u of \ where
        (just _) -> 10
        nothing -> 100

-------------------------------------------------------------------------------

record _:<:_ (a b : Set) : Set where
  field into : a -> b

open _:<:_ {{...}}

instance
  :<:-refl : a :<: a
  :<:-refl .into = id

  :<:-left : a :<: Either a b
  :<:-left .into = left

  :<:-right : {{a :<: c}} -> a :<: Either b c
  :<:-right .into = right <<< into

  HasAdd-Set : HasAdd Set
  HasAdd-Set ._+_ = Either

f' : Nat -> (Nat + String) + Bool
f' 0 = into true
f' 1 = into ""
f' 2 = into (the Nat 0)
f' _ = into false

