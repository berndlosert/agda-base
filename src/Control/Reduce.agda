{-# OPTIONS --type-in-type #-}

module Control.Reduce where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
-- Transducer
-------------------------------------------------------------------------------

Transducer : Set -> Set -> Set
Transducer a b = forall {c} -> Reducer b c -> Reducer a c

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

reduce : {{Foldable t}} -> Reducer a b -> t a -> b
reduce {t} {a} {b} (reducer {c} step init extract) xs =
    foldr go extract xs init
  where
    go : a -> (c -> b) -> c -> b
    go x k z = case step z x of \ where
      (reduced true y) -> extract y
      (reduced false y) -> k $! y

transduce : {{Foldable t}} -> Transducer a b -> Reducer b c -> t a -> c
transduce t r = reduce (t r)

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

reducer' : (c -> a -> c) -> c -> (c -> b) -> Reducer a b
reducer' {c} {a} step init extract = reducer step' init extract
  where
    step' : c -> a -> Reduced c
    step' z x = reduced false (step z x)

intoFold : (b -> a -> b) -> b -> Reducer a b
intoFold step init = reducer' step init id

mapping : (a -> b) -> Transducer a b
mapping f (reducer step init extract) =
  reducer (\ z x -> step z (f x)) init extract

filtering : (a -> Bool) -> Transducer a a
filtering p (reducer step init extract) =
  reducer (\ z x -> if p x then step z x else reduced false z) init extract

concatMapping : {{Foldable t}} -> (a -> t b) -> Transducer a b
concatMapping f (reducer step init extract) =
  reducer (\ z x -> reduced false (reduce (reducer step z id) (f x)) init extract

-------------------------------------------------------------------------------
-- Some reducers
-------------------------------------------------------------------------------

intoLength : Reducer a Nat
intoLength = intoFold (\ n _ -> n + 1) 0

intoList : Reducer a (List a)
intoList = reducer' (\ z x -> z <<< (x ::_)) id (_$ [])

intoNull : Reducer a Bool
intoNull = reducer (\ _ _ -> reduced true false) true id

intoAnd : Reducer Bool Bool
intoAnd =
  reducer (\ z x -> if x then reduced false z else reduced true x) false id

intoOr : Reducer Bool Bool
intoOr =
  reducer (\z x -> if x then reduced true x else reduced false z) false id

module _ {{fn : FromNat a}} where
  intoSum : {{Add a}} -> {{FromNatConstraint {{fn}} 0}} -> Reducer a a
  intoSum = intoFold _+_ 0

  intoProduct : {{Mul a}} -> {{FromNatConstraint {{fn}} 1}} -> Reducer a a
  intoProduct = intoFold _*_ 1
