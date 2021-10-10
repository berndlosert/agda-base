{-# OPTIONS --type-in-type #-}

module Data.Rec where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Free.Signature
open import Data.Signature
open import Data.Fix

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Free.Signature public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a c d : Set
    b : a -> Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- General
-------------------------------------------------------------------------------

General : (a : Set) (b : a -> Set) (c : Set) -> Set
General a b c = Free (signature a b) c

foldGeneral : (c -> d) -> ((x : a) -> (b x -> d) -> d) -> General a b c -> d
foldGeneral done step = \ where
  (finished y _) -> done y
  (roll x arg) -> step x \ n -> foldGeneral done step (toFree (arg n))

interpretGeneral : {{Monad m}}
  -> ((x : a) -> m (b x)) -> General a b c -> m c
interpretGeneral t = foldGeneral pure \ x -> t x >>=_

already : General a b c -> Maybe c
already = interpretGeneral \ _ -> nothing

-------------------------------------------------------------------------------
-- DRec, Rec
-------------------------------------------------------------------------------

DRec : (a : Set) (b : a -> Set) -> Set
DRec a b = (x : a) -> General a b (b x)

Rec : Set -> Set -> Set
Rec a b = DRec a (const b)

call : DRec a b
call x = roll x (pure >>> unFree)

expand : DRec a b -> General a b c -> General a b c
expand f = interpretGeneral f

engine : DRec a b -> Nat -> General a b c -> General a b c
engine f 0 = id
engine f (suc n) = engine f n <<< expand f

petrol : DRec a b -> Nat -> (x : a) -> Maybe (b x)
petrol f n x = already $ engine f n $ f x

{-# TERMINATING #-}
combust : DRec a b -> (x : a) -> b x
combust {a} {b} f x = loop (f x)
  where
    loop : General a b (b x) -> b x
    loop y = maybe (loop (expand f y)) id (already y)
