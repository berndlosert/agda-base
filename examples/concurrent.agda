open import Prelude

open import Control.Concurrent
open import Control.Concurrent.Async
open import Control.Monad.Gen
open import Control.Monad.IO.Class
open import System.IO
open import System.Random

instance
  _ = FromNat-Int

data Foo (a : Type) : Type where
  foo : Unit -> IO a -> Foo a

randomDelay : IO Unit
randomDelay = threadDelay =<< genNatBetween 1000 1000000

action1 : IO Int
action1 = randomDelay *> pure 5

action2 : IO String
action2 = randomDelay *> pure "action2 result"

main : IO Unit
main = do
  res <- race action1 action2
  print res