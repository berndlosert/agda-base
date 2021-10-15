{-# OPTIONS --type-in-type --guardedness #-}

open import Prelude

open import Control.Monad.Iter
open import Data.Foldable
open import Data.List as List using ()
open import System.IO

variable
  a : Set

-- https://hackage.haskell.org/package/free-5.1.7/src/examples/Cabbage.lhs

data Item : Set where
  wolf sheep cabbage farmer : Item

instance
  Eq-Item : Eq Item
  Eq-Item ._==_ = \ where
    wolf wolf -> true
    sheep sheep -> true
    cabbage cabbage -> true
    farmer farmer -> true
    _ _ -> false

  Show-Item : Show Item
  Show-Item .showsPrec d = \ where
    wolf -> showString "wolf"
    sheep -> showString "sheep"
    cabbage -> showString "cabbage"
    farmer -> showString "farmer"

_eats_ : Item -> Item -> Bool
sheep eats cabbage = true
wolf eats sheep = true
_ eats _ = false

Situation : Set
Situation = Pair (List Item) (List Item)

toMaybe : List a -> Maybe a
toMaybe [] = nothing
toMaybe (x :: xs) = just x

initial : Situation
initial = (farmer :: wolf :: sheep :: cabbage :: [] , [])

plusTailOf : List a -> List a -> Pair (Maybe a) (List a)
plusTailOf xs ys = (toMaybe ys , xs <> List.drop 1 ys)

singleOut1 : (a -> Bool) -> List a -> Pair (Maybe a) (List a)
singleOut1 sel = uncurry plusTailOf <<< List.break sel

singleOutAll : List a -> List (Pair (Maybe a) (List a))
singleOutAll = List.zipWith plusTailOf <$> List.inits <*> List.tails

move : Situation -> List Situation
move = move2
  where
    move1 : List Item -> List Item -> _
    move1 as bs = do
      (b , as') <- singleOutAll as
      guard $ and do
        x <- as'
        y <- as'
        pure $ not (x eats y)
      pure (as' , farmer :: [] <> toList b <> bs)

    move2 : _
    move2 sit = case singleOut1 (_== farmer) (fst sit) of \ where
      (just farmer , xs) -> move1 xs (snd sit)
      _ -> case singleOut1 (_== farmer) (snd sit) of \ where
        (just farmer , xs) -> map swap $ move1 xs (fst sit)
        _ -> []

success : Situation -> Bool
success ([] , _) = true
success _ = false

solution2 : Iter Situation
solution2 = solutions' initial
  where
    solutions' : Situation -> Iter Situation
    solutions' = fix \ where
      go a ->
        if success a
          then pure a
          else delay $ asum $ map go (move a)

testSolution2 :
  execIter solution2
  ===
  ([] , farmer :: sheep :: cabbage :: wolf :: [])
testSolution2 = refl
