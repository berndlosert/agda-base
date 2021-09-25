{-# OPTIONS --type-in-type #-}

module Control.Reduce where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Float as Float using ()
open import Data.Foldable hiding (continue; done)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    m t : Set -> Set

-------------------------------------------------------------------------------
-- Reduced
-------------------------------------------------------------------------------

data Reduced (a : Set) : Set where
  reduced : Bool -> a -> Reduced a

instance
  Functor-Reduced : Functor Reduced
  Functor-Reduced .map f (reduced b x) = reduced b (f x)

  Applicative-Reduced : Applicative Reduced
  Applicative-Reduced .pure = reduced false
  Applicative-Reduced ._<*>_ (reduced b f) (reduced b' x) =
    reduced (b && b') (f x)

-------------------------------------------------------------------------------
-- Reducer
-------------------------------------------------------------------------------

data Reducer (a b : Set) : Set where
  reducer : (c -> a -> Reduced c) -> c -> (c -> b) -> Reducer a b

instance
  Functor-Reducer : Functor (Reducer a)
  Functor-Reducer .map f (reducer step init extract) =
    reducer step init (extract >>> f)

  Applicative-Reducer : Applicative (Reducer a)
  Applicative-Reducer .pure x =
    let
      step _ _ = reduced true tt
      init = tt
      extract = const x
    in
      reducer step init extract
  Applicative-Reducer ._<*>_
    (reducer step1 init1 extract1) (reducer step2 init2 extract2) =
        reducer step init extract
      where
        init : _
        init = (init1 , init2)

        extract : _
        extract (f , x) = extract1 f (extract2 x)

        step : _
        step (f , x) y = f seq x seq (| (step1 f y) , (step2 x y) |)

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

reduce : {{Foldable t}} -> Reducer a b -> t a -> b
reduce {t} {a} {b} (reducer {c} step init extract) xs =
    foldr go extract xs init
  where
    go : a -> (c -> b) -> c -> b
    go x k z = case step z x of \ where
      (reduced true y) -> extract y
      (reduced false y) -> k $! y

reducer' : (c -> a -> c) -> c -> (c -> b) -> Reducer a b
reducer' {c} {a} step init extract = reducer step' init extract
  where
    step' : c -> a -> Reduced c
    step' z x = reduced false (step z x)

intoFold : (b -> a -> b) -> b -> Reducer a b
intoFold step init = reducer' step init id

intoSum : {{fn : FromNat a}}
  -> {{Add a}}
  -> {{FromNatConstraint {{fn}} 0}}
  -> Reducer a a
intoSum = intoFold _+_ 0

intoLength : Reducer a Nat
intoLength = intoFold (\ n _ -> n + 1) 0

intoAverage : Reducer Float Float
intoAverage = (| Float.divide intoSum (Float.fromNat <$> intoLength) |)
