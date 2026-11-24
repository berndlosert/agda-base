open import Data.List.Elem
open import Data.String
open import Prelude

test : elemIndex 'c' (unpack "abc") elem2 === 2
test = refl