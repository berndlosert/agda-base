module Test.QC.Fun where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Gen.Class
open import Data.List as List using ()
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
      a b c : Type
      m : Type -> Type

-------------------------------------------------------------------------------
-- Fun
-------------------------------------------------------------------------------

private
  record Fun' (a b : Type) : Type where
    constructor fun'
    field
      graph : List (Tuple a b)
      default : b

Fun = Fun'

fun : {{Eq a}} -> List (Tuple a b) -> b -> Fun a b
fun {a = a} {b = b} graph = fun' (List.foldr insert [] graph)
  where
    insert : (Tuple a b) -> List (Tuple a b) -> List (Tuple a b)
    insert (k , v) kvs =
      if List.any ((_== k) <<< fst) kvs
        then kvs
        else (k , v) :: kvs

applyFun : {{Eq a}} -> Fun a b -> a -> b
applyFun (fun' graph default) x =
  case (List.head (List.filter ((_== x) <<< fst) graph)) \ where
    nothing -> default
    (just (_ , y)) -> y

genFun : {{Eq a}} -> {{MonadGen m}} -> m a -> m b -> m (Fun a b)
genFun ma mb = do
  graph <- genListOfSize 5 (| ma , mb |)
  default <- mb
  pure (fun graph default)

instance
  Show-Fun : {{Show a}} -> {{Show b}} -> Show (Fun a b)
  Show-Fun .showsPrec prec (fun' graph default) = "fun " <> showsPrec prec graph <> " " <> showsPrec prec default
  Show-Fun .show = showDefault