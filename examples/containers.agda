{-# OPTIONS --type-in-type #-}

open import Prelude hiding (List)

open import Data.Container
open import Data.Fix

variable
  a : Set

NaturalC : Container
NaturalC .Shape = Bool
NaturalC .Position false = Void
NaturalC .Position true = Unit

Natural = Fix NaturalC

Z : Natural
Z = toFix (extension false \ ())

S : Natural -> Natural
S n = toFix (extension true (const n))

ListC : Set -> Container
ListC a .Shape = Maybe a
ListC a .Position nothing = Void
ListC a .Position (just _) = Unit

List : Set -> Set
List a = Fix (ListC a)

nil : List a
nil = toFix (extension nothing \ ())

cons : a -> List a -> List a
cons x (toFix (extension nothing p)) = toFix $ extension (just x) (const nil)
cons x (toFix (extension (just y) p)) = toFix $ extension (just x) (\ tt -> let ys = p tt in cons y ys)

length : List a -> Natural
length {a} = foldFix alg
  where
    alg : Extension (ListC a) Natural -> Natural
    alg (extension nothing p) = Z
    alg (extension (just _) p) = S (p tt)
