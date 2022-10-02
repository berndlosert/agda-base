open import Prelude

private
  variable
    a b s : Set

record Moore (s a b : Set) : Set where
  field
    state : s
    transition : s -> a -> s
    output : s -> b

record Moore' (a b : Set) : Set where
  constructor asMoore'
  field
    output : b
    next : a -> Moore' a b

f : Moore s a b -> Moore' a b
f {s} {a} {b} m = asMoore' o go
  where
    o : b
    o = Moore.output m (Moore.state m)
    go : a -> Moore' a b
    go x =
      let q = Moore.transition m (Moore.state m) x
      in asMoore' (Moore.output m q) go
