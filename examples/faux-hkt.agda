open import Prelude hiding (Functor; map)

variable
  a b : Type

record Refunctionalize (f : Type) : Type where
  field TypeConstructor : Type -> Type

open Refunctionalize {{...}}

data ForMaybe : Type where
  forMaybe : ForMaybe

instance
  Refunctionalize-ForMaybe : Refunctionalize ForMaybe
  Refunctionalize-ForMaybe .TypeConstructor = Maybe

record Kind (f a : Type) : Type where
  constructor toKind
  field fromKind : {{Refunctionalize f}} -> TypeConstructor a

open Kind

record Functor (f a b : Type) : Type where
  field
    map : (a -> b) -> Kind f a -> Kind f b

open Functor {{...}}

instance
  Functor-ForMaybe : Functor ForMaybe a b
  Functor-ForMaybe .map f x =
    case (fromKind x) \ where
      (just x) -> toKind $ just (f x)
      nothing -> toKind nothing