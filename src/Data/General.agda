{-# OPTIONS --type-in-type #-}

module Data.General where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a x y : Type
    b : a -> Type
    m : Type -> Type

-------------------------------------------------------------------------------
-- General
-------------------------------------------------------------------------------

data General (a : Type) (b : a -> Type) (x : Type) : Type where
  Tell : x -> General a b x
  Ask : (i : a) -> (b i -> General a b x) -> General a b x

PiG : (a : Type) -> (b : a -> Type) -> Type
PiG a b = (i : a) -> General a b (b i)

fold : (x -> y) -> ((i : a) -> (b i -> y) -> y) -> General a b x -> y
fold pure ask (Tell x) = pure x
fold pure ask (Ask i k) = ask i (\ o -> fold pure ask (k o))

call : PiG a b
call i = Ask i Tell

bind : General a b x -> (x -> General a b y) -> General a b y
bind m f = fold f Ask m

monadMorphism : {{Monad m}} -> (t : (i : a) -> m (b i)) -> General a b x -> m x
monadMorphism t = fold pure \ i -> (t i >>=_)

already : General a b x -> Maybe x
already = monadMorphism (\ i -> Nothing)

instance
  Functor-General : Functor (General a b)
  Functor-General .map f = fold (Tell <<< f) Ask

  Applicative-General : Applicative (General a b)
  Applicative-General .pure = Tell
  Applicative-General ._<*>_ fs xs = bind fs \ f -> map (f $_) xs

  Monad-General : Monad (General a b)
  Monad-General ._>>=_ = bind

expand : PiG a b -> General a b x -> General a b x
expand f = monadMorphism f

engine : PiG a b -> Nat -> General a b x -> General a b x
engine f 0 = id
engine f (Suc n) = engine f n <<< expand f

petrol : PiG a b -> Nat -> (i : a) -> Maybe (b i)
petrol f n i = already $ engine f n $ f i
