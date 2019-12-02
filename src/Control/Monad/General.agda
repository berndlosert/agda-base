{-# OPTIONS --type-in-type #-}

module Control.Monad.General where

open import Data.Product

-- A request/response interaction is a pair (req , callback) where req is some
-- value representing a request and callback is a function that is used to
-- handle the response. Note that the type of the response depends on req.
Interact : (Req : Set) -> (Resp : Req -> Set) -> Set -> Set
Interact Req Resp X = Sigma Req (\ req -> Resp req -> X)

open import Control.Category
open import Data.Functor

instance
  Functor:Interact : {Req : Set} {Resp : Req -> Set}
    -> Endofunctor Sets (Interact Req Resp)
  Functor:Interact .map f (req , callback) = (req , callback >>> f) 

open import Control.Monad.Free

-- General is used to model general recursion.
General : (Req : Set) -> (Resp : Req -> Set) -> Set -> Set
General Req Resp = Free (Interact Req Resp)

open import Control.Monad

instance
  Monad:General : forall {Req Resp} -> Monad Sets (General Req Resp) 
  Monad:General = Monad:Free {{Functor:Interact}}

call : forall {Req Resp} (req : Req) -> General Req Resp (Resp req)
call req = \ alpha -> alpha (req , id) 

-- Dependent function type of general recursive functions.
Pi : (Req : Set) (Resp : Req -> Set) -> Set
Pi Req Resp = (req : Req) -> General Req Resp (Resp req)

open import Data.Function

-- Nondependent function type of general recursive functions.
Fun : (X Y : Set) -> Set
Fun X Y = Pi X (const Y)
