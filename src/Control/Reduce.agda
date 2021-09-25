{-# OPTIONS --type-in-type #-}

module Control.Reduce where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable hiding (continue)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    m t : Set -> Set

-------------------------------------------------------------------------------
-- Reducer
-------------------------------------------------------------------------------

data Reducer (a b : Set) : Set where
  reducer : (c -> a -> Either c c) -> c -> (c -> b) -> Reducer a b

instance
  Functor-Reducer : Functor (Reducer a)
  Functor-Reducer .map f (reducer step init extract) =
    reducer step init (extract >>> f)

  Applicative-Reducer : Applicative (Reducer a)
  Applicative-Reducer .pure x =
    let
      step _ _ = left tt
      init = tt
      extract = const x
    in
      reducer step init extract
  Applicative-Reducer ._<*>_
    (reducer {c} step1 init1 extract1) (reducer {d} step2 init2 extract2) =
        reducer step init extract
      where
        init : _
        init = (right init1 , right init2)

        extract : _
        extract p = extract1 (fromEither (fst p)) (extract2 (fromEither (snd p)))

        step : _
        step (left f , left x) y = left (left f , left x)
        step (right f , left x) y = right (step1 f y , left x)
        step (right f , right x) y = right (step1 f y , step2 x y)
        step (left f , right x) y = right (left f , step2 x y)

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

reduce : {{Foldable t}} -> Reducer a b -> t a -> b
reduce {t} {a} {b} (reducer {c} step init extract) xs =
    foldr go extract xs init
  where
    go : a -> (c -> b) -> c -> b
    go x k z = either extract (k $!_) (step z x)

reducer' : (c -> a -> c) -> c -> (c -> b) -> Reducer a b
reducer' {c} {a} step init extract = reducer step' init extract
  where
    step' : c -> a -> Either c c
    step' z x = right (step z x)

intoFold : (b -> a -> b) -> b -> Reducer a b
intoFold step init = reducer' step init id

intoSum : {{fn : FromNat a}}
  -> {{Add a}}
  -> {{FromNatConstraint {{fn}} 0}}
  -> Reducer a a
intoSum = intoFold _+_ 0

intoLength : Reducer a Nat
intoLength = intoFold (\ n _ -> suc n) 0
