open import Prelude

open import Data.Filterable
open import Data.Monoid.Foldable
open import Data.String.Show

variable
  n : Nat
  a b : Type
  as : List Type

data HList : List Type -> Type where
  [] : HList []
  _::_ : a -> HList as -> HList (a :: as)

Curried : List Type -> Type -> Type
Curried [] b = b
Curried (a :: as) b = a -> Curried as b

curry : (HList as -> b) -> Curried as b
curry {as = as} f with as
... | [] = f []
... | _ :: _ = \ x -> curry (f <<< (x ::_))

data Placeholder : Type -> Type where
  %s : Placeholder String
  %d : Placeholder Nat

data Format : List Type -> Type where
  end : Format []
  str : String -> Format as -> Format as
  placeholder : Placeholder a -> Format as -> Format (a :: as)

record Format' : Type  where
  field
    types : List Type
    format : Format types

fmt : Format (String :: Nat :: [])
fmt = str "My name is " $ placeholder %s $ str ". I am " $ placeholder %d $ str " years old" end

sprintf' : Format as -> HList as -> String
sprintf' end _ = ""
sprintf' (str s fmt) t = s <> sprintf' fmt t
sprintf' (placeholder %s fmt) (s :: t) = s <> sprintf' fmt t
sprintf' (placeholder %d fmt) (n :: t) = show n <> sprintf' fmt t

sprintf : Format as -> Curried as String
sprintf fmt = curry (sprintf' fmt)

_ : sprintf fmt "Foo" 123 === "My name is Foo. I am 123 years old"
_ = refl
