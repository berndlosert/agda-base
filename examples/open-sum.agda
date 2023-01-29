open import Prelude
module open-sum where

-------------------------------------------------------------------------------

module Sum-test where
  open import Data.Open.Sum

  variable
    a b c : Set

  f : Nat -> Sum (Nat :: String :: Bool :: [])
  f 0 = inj true
  f 1 = inj ""
  f 2 = inj (id {Nat} 0)
  f _ = inj false

  g : Sum (Nat :: String :: Bool :: []) -> Nat
  g u = case prj Nat u of \ where
    (just n) -> n
    nothing -> case prj Bool u of \ where
      (just b) -> if b then 1 else 0
      nothing -> case prj String u of \ where
        (just _) -> 1
        nothing -> case prj Nat u of \ where
          (just _) -> 10
          nothing -> 100

-------------------------------------------------------------------------------

module Sum1-test where

  open import Data.Open.Sum1

  variable
    f : Set -> Set
    fs : List (Set -> Set)

  data Expr (f : Set -> Set) : Set where
    In : f (Expr f) -> Expr f

  data Val (e : Set) : Set where
    aVal : Int -> Val e

  data Add (e : Set) : Set where
    anAdd : e -> e -> Add e

  example : Expr (Sum1 (Val :: Add :: []))
  example = In (inj (anAdd (In (inj (aVal 18))) (In (inj (aVal 1219)))))

  inject : {{Member f fs}} -> f (Expr (Sum1 fs)) -> Expr (Sum1 fs)
  inject = In <<< inj

  val : {{Member Val fs}} -> Int -> Expr (Sum1 fs)
  val i = inject (aVal i)

  add : {{Member Add fs}} -> Expr (Sum1 fs) -> Expr (Sum1 fs) -> Expr (Sum1 fs)
  add l r = inject (anAdd l r)

-------------------------------------------------------------------------------

module data-types-a-la-carte-test where

  variable
    a b c : Set

  record _:<:_ (a b : Set) : Set where
    field into : a -> b

  open _:<:_ {{...}}

  instance
    :<:-refl : a :<: a
    :<:-refl .into = id

    :<:-left : a :<: Either a b
    :<:-left .into = left

    :<:-right : {{a :<: c}} -> a :<: Either b c
    :<:-right .into = right <<< into

  -- Does not work.
  -- f' : Nat -> Nat + (String + Bool)
  -- f' 0 = into true
  -- f' 1 = into ""
  -- f' 2 = into (id {Nat} 0)
  -- f' _ = into false
