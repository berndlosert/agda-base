module Control.Reduce where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad
open import Data.Foldable
open import Data.Profunctor

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
  aReduced : Bool -> a -> Reduced a

instance
  Functor-Reduced : Functor Reduced
  Functor-Reduced .map f (aReduced b x) = aReduced b (f x)

  Applicative-Reduced : Applicative Reduced
  Applicative-Reduced .pure = aReduced false
  Applicative-Reduced ._<*>_ (aReduced b f) (aReduced b' x) =
    aReduced (b && b') (f x)

-------------------------------------------------------------------------------
-- Reducer
-------------------------------------------------------------------------------

data Reducer (a b : Set) : Set where
  aReducer : c -> (c -> a -> Reduced c) -> (c -> b) -> Reducer a b

instance
  Functor-Reducer : Functor (Reducer a)
  Functor-Reducer .map f (aReducer init step done) =
    aReducer init step (done >>> f)

  Profunctor-Reducer : Profunctor Reducer
  Profunctor-Reducer .lcmap f (aReducer init step done) =
    let step' acc x = step acc (f x)
    in aReducer init step' done

  Applicative-Reducer : Applicative (Reducer a)
  Applicative-Reducer .pure x =
    aReducer tt (\ _ _ -> aReduced true tt) (const x)
  Applicative-Reducer ._<*>_
    (aReducer init1 step1 done1) (aReducer init2 step2 done2) =
        aReducer init step done
      where
        init : _
        init = (init1 , init2)

        step : _
        step (acc1 , acc2) x =
          acc1 seq acc2 seq (| (step1 acc1 x) , (step2 acc2 x) |)

        done : _
        done (acc1 , acc2) = done1 acc1 (done2 acc2)

  Semigroup-Reducer : {{Semigroup b}} -> Semigroup (Reducer a b)
  Semigroup-Reducer ._<>_ r1 r2 = (| r1 <> r2 |)

  Monoid-Reducer : {{Monoid b}} -> Monoid (Reducer a b)
  Monoid-Reducer .mempty = pure mempty

  Comonad-Reducer : Comonad (Reducer a)
  Comonad-Reducer .extract (aReducer init _ done) = done init
  Comonad-Reducer .extend f = map f <<< cojoin
    where
      cojoin : Reducer a b -> Reducer a (Reducer a b)
      cojoin (aReducer init step done) =
        let done' acc = aReducer acc step done
        in aReducer init step done'

-------------------------------------------------------------------------------
-- Transducer
-------------------------------------------------------------------------------

Transducer : Set -> Set -> Set
Transducer a b = forall {c} -> Reducer b c -> Reducer a c

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

reduce : {{Foldable t}} -> Reducer a b -> t a -> b
reduce {t} {a} {b} (aReducer {c} init step done) xs =
    foldr step' done xs init
  where
    step' : a -> (c -> b) -> c -> b
    step' x k acc = case step acc x of \ where
      (aReduced true acc') -> done acc'
      (aReduced false acc') -> k $! acc'

transduce : {{Foldable t}} -> Transducer a b -> Reducer b c -> t a -> c
transduce t r = reduce (t r)

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

aReducer' : c -> (c -> a -> c) -> (c -> b) -> Reducer a b
aReducer' {c} {a} init step done =
  let step' acc x = aReduced false (step acc x)
  in aReducer init step' done

intoFold : (b -> a -> b) -> b -> Reducer a b
intoFold step init = aReducer' init step id

intoFoldMap : {{Monoid c}} -> (a -> c) -> (c -> b) -> Reducer a b
intoFoldMap f =
  let step acc x = acc <> f x
  in aReducer' mempty step

mapping : (a -> b) -> Transducer a b
mapping f = lcmap f

filtering : (a -> Bool) -> Transducer a a
filtering p (aReducer init step done) =
  let step' acc x = if p x then step acc x else aReduced false acc
  in aReducer init step' done

concatMapping : {{Foldable t}} -> (a -> t b) -> Transducer a b
concatMapping f (aReducer init step done) =
  let step' acc x = aReduced false (reduce (aReducer acc step id) (f x))
  in aReducer init step' done

taking : Nat -> Transducer a a
taking n (aReducer init step done) = aReducer init' step' done'
  where
    init' : _
    init' = (n , init)

    step' : _
    step' (0 , acc) x = aReduced true (0 , acc)
    step' (suc m , acc) x = case step acc x of \ where
      (aReduced true acc') -> aReduced true (suc m , acc')
      (aReduced false acc') -> aReduced false (m , acc')

    done' : _
    done' (_ , acc) = done acc

takingWhile : (a -> Bool) -> Transducer a a
takingWhile p (aReducer init step done) =
  let step' acc x = if p x then step acc x else aReduced true acc
  in aReducer init step' done

dropping : Nat -> Transducer a a
dropping n (aReducer init step done) = aReducer init' step' done'
  where
    init' : _
    init' = (n , init)

    step' : _
    step' (0 , acc) x = map (0 ,_) (step acc x)
    step' (suc n' , acc) x = aReduced false (n' , acc)

    done' : _
    done' (_ , acc) = done acc

droppingWhile : (a -> Bool) -> Transducer a a
droppingWhile p (aReducer init step done) = aReducer init' step' done'
  where
    init' : _
    init' = (false , init)

    step' : _
    step' (false ,  acc) x =
      if p x
        then aReduced false (false , acc)
        else map (true ,_) (step acc x)
    step' (true , acc) x = map (true ,_) (step acc x)

    done' : _
    done' (_ , acc) = done acc

-------------------------------------------------------------------------------
-- Some aReducers
-------------------------------------------------------------------------------

intoLength : Reducer a Nat
intoLength = intoFold (\ n _ -> n + 1) 0

intoList : Reducer a (List a)
intoList = aReducer' id (\ acc x -> acc <<< (x ::_)) (_$ [])

intoNull : Reducer a Bool
intoNull = aReducer true (\ _ _ -> aReduced true false) id

intoAnd : Reducer Bool Bool
intoAnd =
  let step acc x = if x then aReduced false acc else aReduced true x
  in aReducer false step id

intoOr : Reducer Bool Bool
intoOr =
  let step acc x = if x then aReduced true x else aReduced false acc
  in aReducer false step id

intoAll : (a -> Bool) -> Reducer a Bool
intoAll p = mapping p intoAnd

intoAny : (a -> Bool) -> Reducer a Bool
intoAny p = mapping p intoOr

intoSum : {{Num a}} -> Reducer a a
intoSum = intoFold _+_ 0

intoProduct : {{Num a}} -> Reducer a a
intoProduct = intoFold _*_ 1

intoFirst : Reducer a (Maybe a)
intoFirst = aReducer nothing (\ _ x -> aReduced true (just x)) id

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
