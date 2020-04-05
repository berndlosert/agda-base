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

on : (B -> B -> C) -> (A -> B) -> A -> A -> C
on f g x y = f (g x) (g y)

infixr 0 _$_
_$_ : (A -> B) -> A -> B
_$_ = id

infixr 9 _<<<_
_<<<_ : (B -> C) -> (A -> B) -> A -> C
g <<< f = \ a -> g (f a)

infixr 9 _>>>_
_>>>_ : (A -> B) -> (B -> C) -> A -> C
_>>>_ = flip _<<<_
