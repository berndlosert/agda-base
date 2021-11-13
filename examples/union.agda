open import Prelude

open import Data.Union

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
