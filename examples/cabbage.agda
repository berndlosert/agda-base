open import Prelude

open import Control.Monad.Iter
open import Data.Monoid.Foldable
open import Data.List as List using ()
open import Data.String.Show
open import System.IO

variable
  a : Type

-- https://hackage.haskell.org/package/free-5.1.7/src/examples/Cabbage.lhs

data Item : Type where
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
  Show-Item .show = \ where
    wolf -> "wolf"
    sheep -> "sheep"
    cabbage -> "cabbage"
    farmer -> "farmer"
  Show-Item .showsPrec = showsPrecDefault

_eats_ : Item -> Item -> Bool
sheep eats cabbage = true
wolf eats sheep = true
_ eats _ = false

Situation : Type
Situation = Tuple (List Item) (List Item)

toMaybe : List a -> Maybe a
toMaybe [] = nothing
toMaybe (x :: xs) = just x

asFirst : Situation
asFirst = (farmer :: wolf :: sheep :: cabbage :: [] , [])

plusTailOf : List a -> List a -> Tuple (Maybe a) (List a)
plusTailOf xs ys = (toMaybe ys , xs <> List.drop 1 ys)

singleOut1 : (a -> Bool) -> List a -> Tuple (Maybe a) (List a)
singleOut1 sel zs = let (xs , ys) = List.break sel zs in plusTailOf xs ys

singleOutAll : List a -> List (Tuple (Maybe a) (List a))
singleOutAll = List.zipWith plusTailOf <$> List.inits <*> List.tails

move : Situation -> List Situation
move = move2
  where
    move1 : List Item -> List Item -> _
    move1 xs ys = do
      (x , zs) <- singleOutAll xs
      guard $ and do
        x <- zs
        y <- zs
        pure (not (x eats y))
      pure (zs , farmer :: [] <> toList x <> ys)

    move2 : _
    move2 sit = case (singleOut1 (_== farmer) (fst sit)) \ where
      (just farmer , xs) -> move1 xs (snd sit)
      _ -> case (singleOut1 (_== farmer) (snd sit)) \ where
        (just farmer , xs) -> map swap (move1 xs (fst sit))
        _ -> []

success : Situation -> Bool
success ([] , _) = true
success _ = false

solution2 : Iter Situation
solution2 = solutions asFirst
  where
    solutions : Situation -> Iter Situation
    solutions a =
      if success a
        then pure a
        else delay (asum (map solutions (move a)))

testSolution2 :
  execIter solution2
  ===
  ([] , farmer :: sheep :: cabbage :: wolf :: [])
testSolution2 = refl
