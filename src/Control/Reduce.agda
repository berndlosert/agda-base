module Control.Reduce where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad
open import Data.Monoid.Foldable
open import Data.Profunctor

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    m t : Type -> Type

-------------------------------------------------------------------------------
-- Reduced
-------------------------------------------------------------------------------

data Reduced (a : Type) : Type where
  reduced : Bool -> a -> Reduced a

instance
  Functor-Reduced : Functor Reduced
  Functor-Reduced .map f (reduced b x) = reduced b (f x)

  Applicative-Reduced : Applicative Reduced
  Applicative-Reduced .pure = reduced false
  Applicative-Reduced ._<*>_ (reduced b f) (reduced c x) =
    reduced (b && c) (f x)

-------------------------------------------------------------------------------
-- Reducer
-------------------------------------------------------------------------------

data Reducer (a b : Type) : Type where
  reducer : c -> (c -> a -> Reduced c) -> (c -> b) -> Reducer a b

instance
  Functor-Reducer : Functor (Reducer a)
  Functor-Reducer .map f (reducer init step done) =
    reducer init step (done >>> f)

  Profunctor-Reducer : Profunctor Reducer
  Profunctor-Reducer .lcmap f (reducer init step done) =
    let step1 acc x = step acc (f x)
    in reducer init step1 done

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
        step (acc1 , acc2) x =
          seq acc1 (seq acc2 (| (step1 acc1 x) , (step2 acc2 x) |))

        done : _
        done (acc1 , acc2) = done1 acc1 (done2 acc2)

  Semigroup-Reducer : {{Semigroup b}} -> Semigroup (Reducer a b)
  Semigroup-Reducer ._<>_ r1 r2 = (| r1 <> r2 |)

  Monoid-Reducer : {{Monoid b}} -> Monoid (Reducer a b)
  Monoid-Reducer .mempty = pure mempty

  Comonad-Reducer : Comonad (Reducer a)
  Comonad-Reducer .extract (reducer init _ done) = done init
  Comonad-Reducer .extend f = map f <<< cojoin
    where
      cojoin : Reducer a b -> Reducer a (Reducer a b)
      cojoin (reducer init step done) =
        let done1 acc = reducer acc step done
        in reducer init step done1

-------------------------------------------------------------------------------
-- Transducer
-------------------------------------------------------------------------------

Transducer : Type -> Type -> Type
Transducer a b = forall {c} -> Reducer b c -> Reducer a c

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

reduce : {{Foldable t}} -> Reducer a b -> t a -> b
reduce {t} {a} {b} (reducer {c} init step done) xs =
    foldr step' done xs init
  where
    step' : a -> (c -> b) -> c -> b
    step' x k acc = case (step acc x) \ where
      (reduced true acc') -> done acc'
      (reduced false acc') -> k $! acc'

transduce : {{Foldable t}} -> Transducer a b -> Reducer b c -> t a -> c
transduce t r = reduce (t r)

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

reducer' : c -> (c -> a -> c) -> (c -> b) -> Reducer a b
reducer' {c} {a} init step done =
  let step1 acc x = reduced false (step acc x)
  in reducer init step1 done

intoFold : (b -> a -> b) -> b -> Reducer a b
intoFold step init = reducer' init step id

intoFoldMap : {{Monoid c}} -> (a -> c) -> (c -> b) -> Reducer a b
intoFoldMap f =
  let step acc x = acc <> f x
  in reducer' mempty step

mapping : (a -> b) -> Transducer a b
mapping f = lcmap f

filtering : (a -> Bool) -> Transducer a a
filtering p (reducer init step done) =
  let step1 acc x = if p x then step acc x else reduced false acc
  in reducer init step1 done

concatMapping : {{Foldable t}} -> (a -> t b) -> Transducer a b
concatMapping f (reducer init step done) =
  let step1 acc x = reduced false (reduce (reducer acc step id) (f x))
  in reducer init step1 done

taking : Nat -> Transducer a a
taking n (reducer init step done) = reducer init1 step1 done1
  where
    init1 : _
    init1 = (n , init)

    step1 : _
    step1 (0 , acc) x = reduced true (0 , acc)
    step1 (suc m , acc) x = case (step acc x) \ where
      (reduced true acc1) -> reduced true (suc m , acc1)
      (reduced false acc1) -> reduced false (m , acc1)

    done1 : _
    done1 (_ , acc) = done acc

takingWhile : (a -> Bool) -> Transducer a a
takingWhile p (reducer init step done) =
  let step1 acc x = if p x then step acc x else reduced true acc
  in reducer init step1 done

dropping : Nat -> Transducer a a
dropping n (reducer init step done) = reducer init1 step1 done1
  where
    init1 : _
    init1 = (n , init)

    step1 : _
    step1 (0 , acc) x = map (0 ,_) (step acc x)
    step1 (suc n-1 , acc) x = reduced false (n-1 , acc)

    done1 : _
    done1 (_ , acc) = done acc

droppingWhile : (a -> Bool) -> Transducer a a
droppingWhile p (reducer init step done) = reducer init1 step1 done1
  where
    init1 : _
    init1 = (false , init)

    step1 : _
    step1 (false ,  acc) x =
      if p x
        then reduced false (false , acc)
        else map (true ,_) (step acc x)
    step1 (true , acc) x = map (true ,_) (step acc x)

    done1 : _
    done1 (_ , acc) = done acc

-------------------------------------------------------------------------------
-- Any reducers
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

intoSum : {{Monoid (Sum a)}} -> Reducer a a
intoSum = intoFoldMap asSum getSum

intoProduct : {{Monoid (Product a)}} -> Reducer a a
intoProduct = intoFoldMap asProduct getProduct

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
    step (just acc) x = just $ case (cmp acc x) \ where
      greater -> x
      _ -> acc

intoMaximumBy : (a -> a -> Ordering) -> Reducer a (Maybe a)
intoMaximumBy {a} cmp = intoFold step nothing
  where
    step : Maybe a -> a -> Maybe a
    step nothing x = just x
    step (just acc) x = just $ case (cmp acc x) \ where
      less -> x
      _ -> acc
