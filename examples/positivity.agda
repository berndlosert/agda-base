open import Prelude

open import System.IO

data Bad : Set where
  bad : (Bad -> Unit) -> Bad

oops : Bad -> Unit
oops (bad f) = f (bad f)

ohno : Unit
ohno = oops (bad oops)

main : IO Unit
main = print ohno