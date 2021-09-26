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
  reducer : c -> (c -> a -> Reduced c) -> (c -> b) -> Reducer a b

instance
  Functor-Reducer : Functor (Reducer a)
  Functor-Reducer .map f (reducer init step done) =
    reducer init step (done >>> f)

  Applicative-Reducer : Applicative (Reducer a)
  Applicative-Reducer .pure x =
    let
      init = tt
      step _ _ = reduced true tt
      done = const x
    in
      reducer init step done
  Applicative-Reducer ._<*>_
    (reducer init1 step1 done1) (reducer init2 step2 done2) =
        reducer init step done
      where
        init : _
        init = (init1 , init2)

        step : _
        step (f , x) y = f seq x seq (| (step1 f y) , (step2 x y) |)

        done : _
        done (f , x) = done1 f (done2 x)

-------------------------------------------------------------------------------
-- Transducer
-------------------------------------------------------------------------------

Transducer : Set -> Set -> Set
Transducer a b = forall {c} -> Reducer b c -> Reducer a c

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

reduce : {{Foldable t}} -> Reducer a b -> t a -> b
reduce {t} {a} {b} (reducer {c} init step done) xs =
    foldr go done xs init
  where
    go : a -> (c -> b) -> c -> b
    go x k z = case step z x of \ where
      (reduced true y) -> done y
      (reduced false y) -> k $! y

transduce : {{Foldable t}} -> Transducer a b -> Reducer b c -> t a -> c
transduce t r = reduce (t r)

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

reducer' : c -> (c -> a -> c) -> (c -> b) -> Reducer a b
reducer' {c} {a} init step done = reducer init step' done
  where
    step' : c -> a -> Reduced c
    step' z x = reduced false (step z x)

intoFold : (b -> a -> b) -> b -> Reducer a b
intoFold step init = reducer' init step id

mapping : (a -> b) -> Transducer a b
mapping f (reducer init step done) =
  let step' z x = step z (f x)
  in reducer init step' done

filtering : (a -> Bool) -> Transducer a a
filtering p (reducer init step done) =
  let step' z x = if p x then step z x else reduced false z
  in reducer init step' done

concatMapping : {{Foldable t}} -> (a -> t b) -> Transducer a b
concatMapping f (reducer init step done) =
  let step' z x = reduced false (reduce (reducer z step id) (f x))
  in reducer init step' done

taking : Nat -> Transducer a a
taking n (reducer init step done) = reducer init' step' done'
  where
    init' : _
    init' = (n , init)

    step' : _
    step' (0 , z) x = reduced true (0 , z)
    step' (suc m , z) x = case step z x of \ where
      (reduced true z') -> reduced true (suc m , z')
      (reduced false z') -> reduced false (m , z')

    done' : _
    done' (_ , z) = done z

-------------------------------------------------------------------------------
-- Some reducers
-------------------------------------------------------------------------------

intoLength : Reducer a Nat
intoLength = intoFold (\ n _ -> n + 1) 0

intoList : Reducer a (List a)
intoList =
  let
    init = id
    step z x = z <<< (x ::_)
    done = _$ []
  in
    reducer' init step done

intoNull : Reducer a Bool
intoNull =
  let
    init = true
    step _ _ = reduced true false
    done = id
  in
    reducer init step done

intoAnd : Reducer Bool Bool
intoAnd =
  let
    init = false
    step z x = if x then reduced false z else reduced true x
    done = id
  in
    reducer init step done

intoOr : Reducer Bool Bool
intoOr =
  let
    init = false
    step z x = if x then reduced true x else reduced false z
    done = id
  in
    reducer init step done

intoAll : (a -> Bool) -> Reducer a Bool
intoAll p = mapping p intoAnd

intoAny : (a -> Bool) -> Reducer a Bool
intoAny p = mapping p intoOr

module _ {{fn : FromNat a}} where
  intoSum : {{Add a}} -> {{FromNatConstraint {{fn}} 0}} -> Reducer a a
  intoSum = intoFold _+_ 0

  intoProduct : {{Mul a}} -> {{FromNatConstraint {{fn}} 1}} -> Reducer a a
  intoProduct = intoFold _*_ 1
