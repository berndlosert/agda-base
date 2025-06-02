open import Prelude

private
  variable
    a b s : Type

record Moore (s a b : Type) : Type where
  field
    state : s
    transition : s -> a -> s
    output : s -> b

record Moore' (a b : Type) : Type where
  constructor moore'
  field
    output : b
    next : a -> Moore' a b

f : Moore s a b -> Moore' a b
f {s} {a} {b} m = moore' o go
  where
    o : b
    o = Moore.output m (Moore.state m)
    go : a -> Moore' a b
    go x =
      let q = Moore.transition m (Moore.state m) x
      in moore' (Moore.output m q) go
