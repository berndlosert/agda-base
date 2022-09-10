open import Prelude

open import Control.Monad.Reader
open import Data.Functor.Recursive
open import Data.List
open import Data.String using (pack)
open import Data.Tree.Rose
open import System.IO

mySum : List Nat -> Nat
mySum = cata \ where
 [] -> 0
 (x :: sumXs) -> x + sumXs

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
    go : TreeF Nat (Pair (Tree Nat) (Reader Nat String)) -> Reader Nat String
    go (node i trss) = do
      -- trss :: [(Tree Int, Reader Int String)]
      -- ts   :: [Tree Int]
      -- rss  :: [Reader Int String]
      -- ss   :: [String]
      let (ts , rss) = unzip trss
      let count = sum $ map length ts
      ss <- local (_+ 2) $ sequence rss
      indent <- ask
      let s = pack (replicate indent ' ')
           <> "* " <> show i
           <> " (" <> show (the Nat count) <> ")"
      pure $ intercalate "\n" (s :: ss)


main : IO Unit
main = do
  print $ project (the Nat 1 :: 2 :: 3 :: [])
  print $ mySum (10 :: 11 :: 12 :: [])
  putStr $ drawTree $ show <$> myTree
  putStrLn $ pprint4 myTree