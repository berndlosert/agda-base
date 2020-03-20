{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont where

import Control.Monad.ContT as ContT
import Prelude

open ContT using (ContT; ContT:)
open Prelude

private
  variable
    A B R R' : Set

Cont : Set -> Set -> Set
Cont R A = ContT R Identity A

Cont: : ((A -> R) -> R) -> Cont R A
Cont: f = ContT: (\ c -> value (f (runIdentity <<< c)))

run : Cont R A -> (A -> R) -> R
run m k = runIdentity (ContT.run m (value <<< k))

eval : Cont R R -> R
eval m = runIdentity (ContT.eval m)

map' : (R -> R) -> Cont R A -> Cont R A
map' f = ContT.map' (value <<< f <<< runIdentity)

with' : ((B -> R) -> (A -> R)) -> Cont R A -> Cont R B
with' f = ContT.with' ((value <<<_) <<< f <<< (runIdentity <<<_))

reset : Cont R R -> Cont R' R
reset = ContT.reset

shift : ((A -> R) -> Cont R R) -> Cont R A
shift f = ContT.shift (f <<< (runIdentity <<<_))
