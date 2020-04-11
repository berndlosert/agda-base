{-# OPTIONS --type-in-type #-}

module Data.Function where

private variable A B C : Set

Function : Set -> Set -> Set
Function A B = A -> B

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
