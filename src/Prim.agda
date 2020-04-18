{-# OPTIONS --type-in-type #-}

module Prim where

--------------------------------------------------------------------------------
-- Primitive types and type constructors
--------------------------------------------------------------------------------

data Void : Set where

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit; tt to unit)

open import Agda.Builtin.Bool public
  using (Bool; true; false)

open import Agda.Builtin.Nat public
  using (Nat; suc)

open import Agda.Builtin.Int public
  using (Int; pos; negsuc)

open import Agda.Builtin.Float public
  using (Float)

open import Agda.Builtin.Char public
  using (Char)

open import Agda.Builtin.String public
  using (String)

Function : Set -> Set -> Set
Function A B = A -> B

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

{-# COMPILE GHC Either = data Either (Left | Right) #-}

infixr 4 _,_
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair public

{-# FOREIGN GHC type AgdaPair a b = (a, b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Prim.AgdaPair ((,)) #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

open import Agda.Builtin.List public
  using (List; [])
  renaming (_∷_ to _::_)

open import Agda.Builtin.IO public
  using (IO)

--------------------------------------------------------------------------------
-- Primitive functions and operations
--------------------------------------------------------------------------------

private variable A B C : Set

id : A -> A
id a = a

const : A -> B -> A
const a _ = a

flip : (A -> B -> C) -> B -> A -> C
flip f b a = f a b

infixr 0 _$_
_$_ : (A -> B) -> A -> B
_$_ = id

case_of_ : A -> (A -> B) -> B
case_of_ = flip _$_

infixr 9 _<<<_
_<<<_ : (B -> C) -> (A -> B) -> A -> C
g <<< f = \ a -> g (f a)

infixr 9 _>>>_
_>>>_ : (A -> B) -> (B -> C) -> A -> C
_>>>_ = flip _<<<_

infixr 10 if_then_else_
if_then_else_ : Bool -> A -> A -> A
if true then a else _ = a
if false then _ else a = a

not : Bool -> Bool
not false = true
not true = false

infixr 2 _||_
_||_ : Bool -> Bool -> Bool
false || x = x
true || x = true

infixr 3 _&&_
_&&_ : Bool -> Bool -> Bool
false && _ = false
true && x = x
