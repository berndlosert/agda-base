open import Prelude

open import Data.Maybe.Strict as Strict using ()
open import System.IO

x : Maybe String
x = just undefined

y : Strict.Maybe String
y = Strict.just undefined

main : IO Unit
main = do 
  print (maybe "lazy" (\ _ -> "lazy") x)
  -- print (Strict.maybe "strict" (\ _ -> "strict") y)