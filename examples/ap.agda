open import Prelude

open import Control.Applicative.FreeAp
open import Data.String as String using ()
open import System.IO

variable
  a : Type

data Resource : Type -> Type where
  file : FilePath -> Resource String

fetchResource : Resource a -> IO a
fetchResource (file path) = readFile utf8 path

record External (a : Type) : Type where
  constructor external
  field
    {r} : Type
    resource : Resource r
    cont : r -> a

foo : FreeAp External Nat
foo = _+_ <$> liftFreeAp (external (file "foo.txt") String.length) <*> liftFreeAp (external (file "bar.txt") String.length)

listRequiredFiles : FreeAp External a -> List FilePath
listRequiredFiles (Pure _) = []
listRequiredFiles (Ap f (external (file path) _)) = path :: listRequiredFiles f

bar : IO Nat
bar = flip runFreeAp foo \ where
  (external r k) -> k <$> fetchResource r

main : IO Unit
main = do
  print (listRequiredFiles foo)
  writeFile utf8 "foo.txt" "123"
  writeFile utf8 "bar.txt" "4567"
  print =<< bar