open import Prelude

open import Data.Semigroup.First

test1 : just "1" <> just "2" <> just "3" === just "123"
test1 = refl

test2 : just "1" <> nothing <> just "3" === just "13"
test2 = refl


test5 : (asFirst nothing <> asFirst (just "2") <> asFirst (just "3")) === asFirst nothing
test5 = refl