open import Prelude

open import Data.List.Elem
open import Data.String

test : elemIndex 'c' (unpack "abc") elem2 === 2
test = refl