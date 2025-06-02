open import Prelude

open import Data.Monoid.Alt
open import Data.Semigroup.First

test1 : just "1" <> just "2" <> just "3" === just "123"
test1 = refl

test2 : just "1" <> nothing <> just "3" === just "13"
test2 = refl

test3 : (just "1" <|> just "2" <|> just "3") === just "1"
test3 = refl

test4 : (nothing <|> just "2" <|> just "3") === just "2"
test4 = refl

test5 : (asFirst nothing <> asFirst (just "2") <> asFirst (just "3")) === asFirst nothing
test5 = refl

-- The Alt makes it behave like the Alternative instance.
test6 : (asAlt nothing <> asAlt (just "2") <> asAlt (just "3")) === asAlt (just "2")
test6 = refl