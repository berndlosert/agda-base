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
    a x y : Set
    b : a -> Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- General
-------------------------------------------------------------------------------

data General (a : Set) (b : a -> Set) (x : Set) : Set where
  Tell : x -> General a b x
  Ask : (i : a) -> (b i -> General a b x) -> General a b x

PiG : (a : Set) -> (b : a -> Set) -> Set
PiG a b = (i : a) -> General a b (b i)

general : (x -> y) -> ((i : a) -> (b i -> y) -> y) -> General a b x -> y
general tell ask (Tell x) = tell x
general tell ask (Ask i k) = ask i (\ o -> general tell ask (k o))

call : PiG a b
call i = Ask i Tell

private
  bind : General a b x -> (x -> General a b y) -> General a b y
  bind m f = general f Ask m

interpretGeneral : {{Monad m}} -> (t : (i : a) -> m (b i)) -> General a b x -> m x
interpretGeneral t = general pure \ i -> (t i >>=_)

already : General a b x -> Maybe x
already = interpretGeneral (\ i -> Nothing)

instance
  Functor-General : Functor (General a b)
  Functor-General .map f = general (Tell <<< f) Ask

  Applicative-General : Applicative (General a b)
  Applicative-General .pure = Tell
  Applicative-General ._<*>_ fs xs = bind fs \ f -> map (f $_) xs

  Monad-General : Monad (General a b)
  Monad-General ._>>=_ = bind

expand : PiG a b -> General a b x -> General a b x
expand f = interpretGeneral f

engine : PiG a b -> Nat -> General a b x -> General a b x
engine f 0 = id
engine f (Suc n) = engine f n <<< expand f

petrol : PiG a b -> Nat -> (i : a) -> Maybe (b i)
petrol f n i = already $ engine f n $ f i
