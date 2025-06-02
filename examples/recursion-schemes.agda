open import Prelude

open import Control.Monad.Reader
open import Data.Functor.Compose
open import Data.Functor.Recursive
open import Data.List
open import Data.String using (pack)
open import Data.Tree.Rose
open import Debug
open import Data.String.Show
open import System.IO

variable
  a : Type

mySum : List Nat -> Nat
mySum = cata \ where
 (asCompose nothing) -> 0
 (asCompose (just (x , sumXs))) -> x + sumXs

myTree : Tree Nat
myTree = node 0 (
  node 1 [] :: node 2 [] :: node 3 (
    node 31 (
      node 311 (
        node 3111 [] :: node 3112 [] :: []
       ) :: []
      ) :: []
    ) :: []
  )

pprint4 : Tree Nat -> String
pprint4 = flip runReader 0 <<< para go
  where
    go : Base (Tree Nat) (Tuple (Tree Nat) (Reader Nat String)) -> Reader Nat String
    go (asCompose (i , trss)) = do
      -- trss :: [(Tree Int, Reader Int String)]
      -- ts   :: [Tree Int]
      -- rss  :: [Reader Int String]
      -- ss   :: [String]
      let (ts , rss) = unzip trss
      let count = sum (map length ts)
      ss <- withReader (_+ 2) (sequence rss)
      indent <- ask
      let s = pack (replicate indent ' ')
           <> "* " <> show i
           <> " (" <> show count <> ")"
      pure (intercalate "\n" (s :: ss))

suff : {{Show a}} -> List a -> List (List a)
suff {a} = para go
  where
    go : Base (List a) (Tuple (List a) (List (List a))) -> List (List a)
    go (asCompose nothing) = []
    go (asCompose (just (x , (xs , suffxs)))) = xs :: suffxs

sum' : List Nat -> Nat
sum' xs = flip runReader nothing (cata go xs)
  where
    go : Base (List Nat) (Reader (Maybe Nat) Nat) -> Reader (Maybe Nat) Nat
    go (asCompose nothing) = pure 0
    go (asCompose (just (x , r))) = do
      prev <- ask
      r' <- withReader (const (just x)) r
      trace ("prev: " <> show prev) (pure (x + r'))

main : IO Unit
main = do
  --print (project (1 :: 2 :: 3 :: []))
  --print (mySum (10 :: 11 :: 12 :: []))
  --putStr (drawTree (show <$> myTree))
  --putStrLn (pprint4 myTree)
  --print (suff (1 :: 2 :: 3 :: []))
  print (sum' (1 :: 2 :: 3 :: 4 :: []))
