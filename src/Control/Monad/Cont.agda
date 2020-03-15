{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont where

import Control.Monad.Trans.ContT as ContT
import Prelude

open ContT using (ContT; ContT:)
open Prelude

private
  variable
    A B R R' : Set

Cont : Set -> Set -> Set
Cont R A = ContT R Identity A

Cont: : ((A -> R) -> R) -> Cont R A
Cont: f = ContT: (\ c -> Identity: (f (Identity.run <<< c)))

run : Cont R A -> (A -> R) -> R
run m k = Identity.run (ContT.run m (Identity: <<< k))

eval : Cont R R -> R
eval m = Identity.run (ContT.eval m)

map' : (R -> R) -> Cont R A -> Cont R A
map' f = ContT.map' (Identity: <<< f <<< Identity.run)

with' : ((B -> R) -> (A -> R)) -> Cont R A -> Cont R B
with' f = ContT.with' ((Identity: <<<_) <<< f <<< (Identity.run <<<_))

reset : Cont R R -> Cont R' R
reset = ContT.reset

shift : ((A -> R) -> Cont R R) -> Cont R A
shift f = ContT.shift (f <<< (Identity.run <<<_))
