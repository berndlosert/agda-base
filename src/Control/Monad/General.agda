{-# OPTIONS --type-in-type #-}

module Control.Monad.General where

-- A request/response interaction is a pair (req , callback) where req is some
-- value representing a request and callback is a function that is used to
-- handle the response. Note that the type of the response depends on req.

open import Data.Tuple

Interact : (Req : Set) -> (Resp : Req -> Set) -> Set -> Set
Interact Req Resp X = Sigma Req (\ req -> Resp req -> X)

-- General is used to model general recursion.

open import Control.Category
open import Control.Monad.Free

General : (Req : Set) -> (Resp : Req -> Set) -> Set -> Set
General Req Resp = Free (Interact Req Resp)

call : forall {Req Resp} -> (req : Req) -> General Req Resp (Resp req)
call req = Free: \ t -> t (req , id)

-- Dependent function type of general recursive functions.

Pi : (Req : Set) (Resp : Req -> Set) -> Set
Pi Req Resp = (req : Req) -> General Req Resp (Resp req)

-- Nondependent function type of general recursive functions.

open import Data.Function

Fun : (X Y : Set) -> Set
Fun X Y = Pi X (const Y)

-- This instance is for exporting purposes only.

open import Control.Monad

instance
  Monad:General : forall {Req Resp} -> Monad Sets (General Req Resp)
  Monad:General = Monad:Free
