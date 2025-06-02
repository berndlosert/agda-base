open import Prelude

open import Data.Monoid.Foldable
open import Data.String.Show

private
  variable
    a : Type

data Free (a : Type) : Type where
  neutral : Free a
  singleton : a -> Free a
  combine : Free a -> Free a -> Free a

neutralize : Free a -> Free a
neutralize (combine neutral x) = x
neutralize (combine x neutral) = x
neutralize x = x

rassoc : Free a -> Free a
rassoc (combine (combine x y) z) = combine x (combine y z)
rassoc x = x

lassoc : Free a -> Free a
lassoc (combine x (combine y z)) = combine (combine x y) z
lassoc x = x

instance
  Show-Free : {{Show a}} -> Show (Free a)
  Show-Free .show = showDefault
  Show-Free .showsPrec prec = \ where
    neutral -> "neutral"
    (singleton x) -> showsUnaryWith showsPrec "singleton" prec x
    (combine x y) -> showsBinaryWith showsPrec showsPrec "combine" prec x y

  Semigroup-Free : Semigroup (Free a)
  Semigroup-Free ._<>_ = combine

  Monoid-Free : Monoid (Free a)
  Monoid-Free .mempty = neutral

  Foldable-Free : Foldable Free
  Foldable-Free .foldMap f = \ where
    neutral -> mempty
    (singleton x) -> f x
    (combine x y) -> foldMap f x <> foldMap f y

reverse : Free a -> Free a
reverse (combine x y) = combine (reverse x) (reverse y)
reverse x = x

fromList : List a -> Free a
fromList [] = neutral
fromList (x :: xs) = combine (singleton x) (fromList xs)

freeToList : Free a -> List a
freeToList xs = case (rassoc (neutralize xs)) \ where
  neutral -> []
  (singleton x) -> x :: []
  (combine (singleton x) y) -> x :: (freeToList y)
  (combine x y) -> freeToList x <> freeToList y
