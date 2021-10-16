{-# OPTIONS --type-in-type #-}

module Control.Reduce where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable

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
    reducer tt (\ _ _ -> reduced true tt) (const x)
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
    foldr step' done xs init
  where
    step' : a -> (c -> b) -> c -> b
    step' x k acc = case step acc x of \ where
      (reduced true acc') -> done acc'
      (reduced false acc') -> k $! acc'

transduce : {{Foldable t}} -> Transducer a b -> Reducer b c -> t a -> c
transduce t r = reduce (t r)

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

reducer' : c -> (c -> a -> c) -> (c -> b) -> Reducer a b
reducer' {c} {a} init step done =
  let step' acc x = reduced false (step acc x)
  in reducer init step' done

intoFold : (b -> a -> b) -> b -> Reducer a b
intoFold step init = reducer' init step id

intoFoldMap : {{Monoid c}} -> (a -> c) -> (c -> b) -> Reducer a b
intoFoldMap f =
  let step acc x = acc <> f x
  in reducer' mempty step

mapping : (a -> b) -> Transducer a b
mapping f (reducer init step done) =
  let step' acc x = step acc (f x)
  in reducer init step' done

filtering : (a -> Bool) -> Transducer a a
filtering p (reducer init step done) =
  let step' acc x = if p x then step acc x else reduced false acc
  in reducer init step' done

concatMapping : {{Foldable t}} -> (a -> t b) -> Transducer a b
concatMapping f (reducer init step done) =
  let step' acc x = reduced false (reduce (reducer acc step id) (f x))
  in reducer init step' done

taking : Nat -> Transducer a a
taking n (reducer init step done) = reducer init' step' done'
  where
    init' : _
    init' = (n , init)

    step' : _
    step' (0 , acc) x = reduced true (0 , acc)
    step' (suc m , acc) x = case step acc x of \ where
      (reduced true acc') -> reduced true (suc m , acc')
      (reduced false acc') -> reduced false (m , acc')

    done' : _
    done' (_ , acc) = done acc

takingWhile : (a -> Bool) -> Transducer a a
takingWhile p (reducer init step done) =
  let step' acc x = if p x then step acc x else reduced true acc
  in reducer init step' done

dropping : Nat -> Transducer a a
dropping n (reducer init step done) = reducer init' step' done'
  where
    init' : _
    init' = (n , init)

    step' : _
    step' (0 , acc) x = map (0 ,_) (step acc x)
    step' (suc n' , acc) x = reduced false (n' , acc)

    done' : _
    done' (_ , acc) = done acc

droppingWhile : (a -> Bool) -> Transducer a a
droppingWhile p (reducer init step done) = reducer init' step' done'
  where
    init' : _
    init' = (false , init)

    step' : _
    step' (false ,  acc) x =
      if p x
        then reduced false (false , acc)
        else map (true ,_) (step acc x)
    step' (true , acc) x = map (true ,_) (step acc x)

    done' : _
    done' (_ , acc) = done acc

-------------------------------------------------------------------------------
-- Some reducers
-------------------------------------------------------------------------------

intoLength : Reducer a Nat
intoLength = intoFold (\ n _ -> n + 1) 0

intoList : Reducer a (List a)
intoList = reducer' id (\ acc x -> acc <<< (x ::_)) (_$ [])

intoNull : Reducer a Bool
intoNull = reducer true (\ _ _ -> reduced true false) id

intoAnd : Reducer Bool Bool
intoAnd =
  let step acc x = if x then reduced false acc else reduced true x
  in reducer false step id

intoOr : Reducer Bool Bool
intoOr =
  let step acc x = if x then reduced true x else reduced false acc
  in reducer false step id

intoAll : (a -> Bool) -> Reducer a Bool
intoAll p = mapping p intoAnd

intoAny : (a -> Bool) -> Reducer a Bool
intoAny p = mapping p intoOr

intoSum : {{HasAdd a}} -> {{HasNat 0 a}} -> Reducer a a
intoSum = intoFold _+_ 0

intoProduct : {{HasMul a}} -> {{HasNat 1 a}} -> Reducer a a
intoProduct = intoFold _*_ 1

intoFirst : Reducer a (Maybe a)
intoFirst = reducer nothing (\ _ x -> reduced true (just x)) id

intoLast : Reducer a (Maybe a)
intoLast = intoFold (const just) nothing

intoElem : {{Eq a}} -> a -> Reducer a Bool
intoElem x = intoAny (_== x)

intoFind : (a -> Bool) -> Reducer a (Maybe a)
intoFind p = filtering p intoFirst

intoMinimum : {{Ord a}} -> Reducer a (Maybe a)
intoMinimum {a} = intoFold step nothing
  where
    step : Maybe a -> a -> Maybe a
    step nothing x = just x
    step (just acc) x = just (min acc x)

intoMaximum : {{Ord a}} -> Reducer a (Maybe a)
intoMaximum {a} = intoFold step nothing
  where
    step : Maybe a -> a -> Maybe a
    step nothing x = just x
    step (just acc) x = just (max acc x)

intoMinimumBy : (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMinimumBy {a} cmp = intoFold step nothing
  where
    step : Maybe a -> a -> Maybe a
    step nothing x = just x
    step (just acc) x = just $ case cmp acc x of \ where
      GT -> x
      _ -> acc

intoMaximumBy : (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMaximumBy {a} cmp = intoFold step nothing
  where
    step : Maybe a -> a -> Maybe a
    step nothing x = just x
    step (just acc) x = just $ case cmp acc x of \ where
      LT -> x
      _ -> acc
