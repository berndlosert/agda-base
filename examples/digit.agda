open import Prelude

open import Data.Char
open import System.IO

data AsDigit : Char -> Set where
  as0 : {c : Char} -> c === '0' -> AsDigit '0'
  as1 : {c : Char} -> c === '1' -> AsDigit '1'
  as2 : {c : Char} -> c === '2' -> AsDigit '2'
  as3 : {c : Char} -> c === '3' -> AsDigit '3'
  as4 : {c : Char} -> c === '4' -> AsDigit '4'
  as5 : {c : Char} -> c === '5' -> AsDigit '5'
  as6 : {c : Char} -> c === '6' -> AsDigit '6'
  as7 : {c : Char} -> c === '7' -> AsDigit '7'
  as8 : {c : Char} -> c === '8' -> AsDigit '8'
  as9 : {c : Char} -> c === '9' -> AsDigit '9'

asDigit : {{Partial}} -> (c : Char) -> {{Assert $ isDigit c}} -> AsDigit c  
asDigit '0' = as0 refl
asDigit '1' = as1 refl
asDigit '2' = as2 refl
asDigit '3' = as3 refl
asDigit '4' = as4 refl
asDigit '5' = as5 refl
asDigit '6' = as6 refl
asDigit '7' = as7 refl
asDigit '8' = as8 refl
asDigit '9' = as9 refl

toDigit' : (c : Char) -> {{Assert $ isDigit c}} -> Nat
toDigit' c with unsafe asDigit c
... | as0 refl = 0
... | as1 refl = 1
... | as2 refl = 2
... | as3 refl = 3
... | as4 refl = 4
... | as5 refl = 5
... | as6 refl = 6
... | as7 refl = 7
... | as8 refl = 8
... | as9 refl = 9

main : IO Unit
main = print (toDigit '5')
