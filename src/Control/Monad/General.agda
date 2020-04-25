{-# OPTIONS --type-in-type #-}

module Control.Monad.General where

open import Control.Monad.Free
open import Prelude

-- A request/response interaction consists of a request and a callback for
-- handling the response to the request.
record Interaction (Req : Set) (Resp : Req -> Set) (X : Set) : Set where
  constructor Interaction:
  field
    request : Req
    callback : Resp request -> X

-- General is used to model general recursion.
General : (Req : Set) -> (Resp : Req -> Set) -> Set -> Set
General Req Resp = Free (Interaction Req Resp)

call : ∀ {Req Resp} -> (req : Req) -> General Req Resp (Resp req)
call req = Free: λ t -> t (Interaction: req id)

-- Dependent function type of general recursive functions.
Pi : (Req : Set) (Resp : Req -> Set) -> Set
Pi Req Resp = (req : Req) -> General Req Resp (Resp req)

-- Nondependent function type of general recursive functions.
Fun : (X Y : Set) -> Set
Fun X Y = Pi X (const Y)

instance
  monadGeneral : ∀ {Req Resp} -> Monad (General Req Resp)
  monadGeneral = monadFree
