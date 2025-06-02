module Data.Tree.Balanced.TwoThree where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Monoid.Foldable
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

data Tree (a : Type) : Type where
  leaf : Tree a
  two : Tree a -> a -> Tree a -> Tree a
  three : Tree a -> a -> Tree a -> a -> Tree a -> Tree a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Tree : Foldable Tree
  Foldable-Tree .foldMap f = \ where
    leaf ->
      mempty
    (two l x r) ->
      foldMap f l <> f x <> foldMap f r
    (three l x m y r) ->
      foldMap f l <> f x <> foldMap f m <> f y <> foldMap f r

  Eq-Tree : {{Eq a}} -> Eq (Tree a)
  Eq-Tree ._==_ t1 t2 = toList t1 == toList t2

  Show-Tree : {{Show a}} -> Show (Tree a)
  Show-Tree .show = showDefault
  Show-Tree .showsPrec prec leaf = "leaf"
  Show-Tree .showsPrec prec (two l x r) =
    let
      showTree = showsPrec appPrec+1
      showVal = showsPrec appPrec+1
    in
      showParen (prec > appPrec)
        ("two " <> showTree l <> " " <> showVal x <> " " <> showTree r)
  Show-Tree .showsPrec prec (three l x m y r) =
    let
      showTree = showsPrec appPrec+1
      showVal = showsPrec appPrec+1
    in
      showParen (prec > appPrec)
        ("three " <> showTree l <> " " <> showVal x <> " " <> showTree m <> " " <> showVal y <> " " <> showTree r)

-------------------------------------------------------------------------------
-- Constructor predicates
-------------------------------------------------------------------------------

isLeaf : Tree a -> Bool
isLeaf leaf = true
isLeaf _ = false

isTwo : Tree a -> Bool
isTwo (two _ _ _) = true
isTwo _ = false

isThree : Tree a -> Bool
isThree (three _ _ _ _ _) = true
isThree _ = false

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Tree a
empty = leaf

singleton : a -> Tree a
singleton x = two leaf x leaf

-------------------------------------------------------------------------------
-- Helpers for inserting and deleting
-------------------------------------------------------------------------------

private
  data TreeContext (a : Type) : Type where
    twoLeft : a -> Tree a -> TreeContext a
    twoRight : Tree a -> a -> TreeContext a
    threeLeft : a -> Tree a -> a -> Tree a -> TreeContext a
    threeMiddle : Tree a -> a -> a -> Tree a -> TreeContext a
    threeRight : Tree a -> a -> Tree a -> a -> TreeContext a

  data KickUp (a : Type) : Type where
    toKickUp : Tree a -> a -> Tree a -> KickUp a

  fromZipper : List (TreeContext a) -> Tree a -> Tree a
  fromZipper [] t = t
  fromZipper (h :: ctx) t =
    case h \ where
      (twoLeft x r) -> fromZipper ctx (two t x r)
      (twoRight l x) -> fromZipper ctx (two l x t)
      (threeLeft x m y r) -> fromZipper ctx (three t x m y r)
      (threeMiddle l x y r) -> fromZipper ctx (three l x t y r)
      (threeRight l x m y) -> fromZipper ctx (three l x m y t)

-------------------------------------------------------------------------------
-- Inserting
-------------------------------------------------------------------------------

insert : {{Ord a}} -> a -> Tree a -> Tree a
insert {a} v = down []
  where
    up : List (TreeContext a) -> KickUp a -> Tree a
    up [] (toKickUp l x r) = two l x r
    up (h :: ctx) kup =
      case (h , kup) \ where
        (twoLeft x r , toKickUp l w m) ->
          fromZipper ctx (three l w m x r)
        (twoRight l x , toKickUp m w r) ->
          fromZipper ctx (three l x m w r)
        (threeLeft x c y d , toKickUp a w b) ->
          up ctx (toKickUp (two a w b) x (two c y d))
        (threeMiddle a x y d , toKickUp b w c) ->
          up ctx (toKickUp (two a x b) w (two c y d))
        (threeRight a x b y , toKickUp c w d) ->
          up ctx (toKickUp (two a x b) y (two c w d))

    down : List (TreeContext a) -> Tree a -> Tree a
    down ctx leaf = up ctx (toKickUp leaf v leaf)
    down ctx (two l x r) =
      case (compare v x) \ where
        equal -> fromZipper ctx (two l v r)
        less -> down (twoLeft x r :: ctx) l
        greater -> down (twoRight l x :: ctx) r
    down ctx (three l x m y r) =
      case (compare v x , compare v y) \ where
        (equal , _) -> fromZipper ctx (three l v m y r)
        (_ , equal) -> fromZipper ctx (three l x m v r)
        (less , _) -> down (threeLeft x m y r :: ctx) l
        (greater , less) -> down (threeMiddle l x y r :: ctx) m
        (_ , _) -> down (threeRight l x m y :: ctx) r

-------------------------------------------------------------------------------
-- Deleting
-------------------------------------------------------------------------------

pop : {{Ord a}} -> a -> Tree a -> Maybe (Tuple a (Tree a))
pop {a} v = down []
  where
    up : List (TreeContext a) -> Tree a -> Tree a
    up [] t = t
    up (h :: ctx) t =
      case (h , t) \ where
        (twoLeft x leaf , leaf) ->
          fromZipper ctx (two leaf x leaf)
        (twoRight leaf x , leaf) ->
          fromZipper ctx (two leaf x leaf)
        (twoLeft x (two m y r) , l) ->
          up ctx (three l x m y r)
        (twoRight (two l x m) y , r) ->
          up ctx (three l x m y r)
        (twoLeft x (three b y c z d) , a) ->
          fromZipper ctx (two (two a x b) y (two c z d))
        (twoRight (three a x b y c) z , d) ->
          fromZipper ctx (two (two a x b) y (two c z d))
        (threeLeft x leaf y leaf , leaf) ->
          fromZipper ctx (three leaf x leaf y leaf)
        (threeMiddle leaf x y leaf , leaf) ->
          fromZipper ctx (three leaf x leaf y leaf)
        (threeRight leaf x leaf y , leaf) ->
          fromZipper ctx (three leaf x leaf y leaf)
        (threeLeft x (two b y c) z d , a) ->
          fromZipper ctx (two (three a x b y c) z d)
        (threeMiddle (two a x b) y z d , c) ->
          fromZipper ctx (two (three a x b y c) z d)
        (threeMiddle a x y (two c z d) , b) ->
          fromZipper ctx (two a x (three b y c z d))
        (threeRight a x (two b y c) z , d) ->
          fromZipper ctx (two a x (three b y c z d))
        (threeLeft w (three b x c y d) z e , a) ->
          fromZipper ctx (three (two a w b) x (two c y d) z e)
        (threeMiddle (three a w b x c) y z e , d) ->
          fromZipper ctx (three (two a w b) x (two c y d) z e)
        (threeMiddle a w x (three c y d z e) , b) ->
          fromZipper ctx (three a w (two b x c) y (two d z e))
        (threeRight a w (three b x c y d) z , e) ->
          fromZipper ctx (three a w (two b x c) y (two d z e))
        (_ , _) -> t

    maxNode : Tree a -> Maybe a
    maxNode = \ where
      leaf -> nothing
      (two _ x leaf) -> just x
      (two _ _ r) -> maxNode r
      (three _ _ _ x leaf) -> just x
      (three _ _ _ _ r) -> maxNode r

    removeMaxNode : List (TreeContext a) -> Tree a -> Tree a
    removeMaxNode ctx = \ where
      (two leaf _ leaf) ->
        up ctx leaf
      (two l x r@(two _ _ _)) ->
        removeMaxNode (twoRight l x :: ctx) r
      (two l x r@(three _ _ _ _ _)) ->
        removeMaxNode (twoRight l x :: ctx) r
      (three leaf x leaf _ leaf) ->
        up (twoRight leaf x :: ctx) leaf
      (three l x m y r@(two _ _ _)) ->
        removeMaxNode (threeRight l x m y :: ctx) r
      (three l x m y r@(three _ _ _ _ _)) ->
        removeMaxNode (threeRight l x m y :: ctx) r
      t -> t

    down : List (TreeContext a) -> Tree a -> Maybe (Tuple a (Tree a))
    down ctx leaf = nothing
    down ctx (two l x r) =
      case (l , r , compare v x) \ where
        (_ , leaf , equal) ->
          just (x , up ctx leaf)
        (l1 , _ , equal) -> do
          y <- maxNode l1
          just (x , removeMaxNode (twoLeft y r :: ctx) l1)
        (_ , _ , less) ->
          down (twoLeft x r :: ctx) l
        (_ , _ , _ ) ->
          down (twoRight l x :: ctx) r
    down ctx (three l x m y r) =
      case (l , m , r , compare v x , compare v y) \ where
        (leaf , leaf , leaf , equal , _) ->
          just (x , fromZipper ctx (two leaf y leaf))
        (leaf , leaf , leaf , _ , equal) ->
          just (y , fromZipper ctx (two leaf x leaf))
        (l1 , _ , _ , equal , _) -> do
          z <- maxNode l1
          just (x , removeMaxNode (threeLeft z m y r :: ctx) l1)
        (_ , m1 , _ , _ , equal) -> do
          z <- maxNode m1
          just (x , removeMaxNode (threeMiddle l x z r :: ctx) m1)
        (_ , _ , _ ,  less , _) ->
          down (threeLeft x m y r :: ctx) l
        (_ , _ , _ ,  greater , less) ->
          down (threeMiddle l x y r :: ctx) m
        (_ , _ , _ ,  _ , _ ) ->
          down (threeRight l x m y :: ctx) r

delete : {{Ord a}} -> a -> Tree a -> Tree a
delete x t = maybe t snd (pop x t)

-------------------------------------------------------------------------------
-- Querying
-------------------------------------------------------------------------------

query : (a -> Ordering) -> Tree a -> Maybe a
query _ leaf = nothing
query f (two l x r) =
  case (f x) \ where
    equal -> just x
    less -> query f l
    greater -> query f r
query f (three l x m y r) =
  case (f x , f y) \ where
    (equal , _) -> just x
    (less , _) -> query f l
    (greater , equal) -> just y
    (greater , less) -> query f m
    (greater , greater) -> query f r

lookup : {{Ord a}} -> a -> Tree (Tuple a b) -> Maybe b
lookup x = maybe nothing (just <<< snd) <<< query (compare x <<< fst)

member : {{Ord a}} -> a -> Tree a -> Bool
member x = maybe false (const true) <<< query (compare x)

-------------------------------------------------------------------------------
--  Misc.
-------------------------------------------------------------------------------

fromList : {{Ord a}} -> List a -> Tree a
fromList xs = foldr insert xs leaf

map : {{Ord b}} -> (a -> b) -> Tree a -> Tree b
map f = fromList <<< Prelude.map f <<< toList

merge : {{Ord a}} -> Tree a -> Tree a -> Tree a
merge t1 t2 = foldr insert t1 t2

filter : {{Ord a}} -> (a -> Bool) -> Tree a -> Tree a
filter p leaf = leaf
filter p (two l x r) =
  let
    l1 = filter p l
    r1 = filter p r
  in
    if p x then two l1 x r1 else merge l1 r1
filter p (three l x m y r) =
  let
    l1 = filter p l
    m1 = filter p m
    r1 = filter p r
  in case (p x , p y) \ where
    (false , false) -> merge (merge l1 m1) r1
    (true , true) -> three l1 x m1 y r1
    (false , true) -> two (merge l1 m1) y r1
    (true , false) -> two l1 x (merge m1 r1)
