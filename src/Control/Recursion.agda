{-# OPTIONS --type-in-type #-}

module Control.Recursion where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Signature
-------------------------------------------------------------------------------

record Signature : Set where
  constructor aSignature
  field
    Symbol : Set
    Arity : Symbol -> Set

open Signature public

-- The aSignature consisting of one symbol tt representing the id function.
IdS : Signature
IdS .Symbol = Unit
IdS .Arity = const Unit

-- ConstS a is the aSignature where each x : a is a constant symbol.
ConstS : Set -> Signature
ConstS a .Symbol = a
ConstS a .Arity = const Void

instance
  HasAdd-Signature : HasAdd Signature
  HasAdd-Signature ._+_ sig sig' = \ where
    .Symbol -> Either (Symbol sig) (Symbol sig')
    .Arity -> either (Arity sig) (Arity sig')

  HasMul-Signature : HasMul Signature
  HasMul-Signature ._*_ sig sig' = \ where
    .Symbol -> Pair (Symbol sig) (Symbol sig')
    .Arity (symb , symb') -> Either (Arity sig symb) (Arity sig' symb')

-------------------------------------------------------------------------------
-- Operation
-------------------------------------------------------------------------------

record Operation (sig : Signature) (a : Set) : Set where
  constructor anOperation
  field
    symbol : Symbol sig
    argument : Arity sig symbol -> a

open Operation public

instance
  Functor-Operation : {sig : Signature} -> Functor (Operation sig)
  Functor-Operation .map f (anOperation symb arg) = anOperation symb (f <<< arg)

-------------------------------------------------------------------------------
-- Algebra
-------------------------------------------------------------------------------

Algebra : Signature -> Set -> Set
Algebra sig a = Operation sig a -> a

-------------------------------------------------------------------------------
-- Fix
-------------------------------------------------------------------------------

record Fix (sig : Signature) : Set where
  inductive
  pattern
  constructor aFix
  field unFix : Operation sig (Fix sig)

open Fix public

pattern sup op arg = aFix (anOperation op arg)

foldFix : {sig : Signature} -> Algebra sig a -> Fix sig -> a
foldFix alg (sup op arg) =
  let arg' x = foldFix alg (arg x)
  in alg (anOperation op arg')
