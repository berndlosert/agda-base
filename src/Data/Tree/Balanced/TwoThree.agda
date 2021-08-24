{-# OPTIONS --type-in-type #-}

module Data.Tree.Balanced.TwoThree where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable
open import Data.Refined

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
  Leaf : Tree a
  Two : Tree a -> a -> Tree a -> Tree a
  Three : Tree a -> a -> Tree a -> a -> Tree a -> Tree a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Validation-Nonempty-Tree : Validation Nonempty (Tree a)
  Validation-Nonempty-Tree .validate _ Leaf = False
  Validation-Nonempty-Tree .validate _ _ = True

  Foldable-Tree : Foldable Tree
  Foldable-Tree .foldr f z = \ where
    Leaf -> z
    (Two l x r) -> foldr f (f x (foldr f z r)) l
    (Three l x m y r) -> foldr f (f x (foldr f (f y (foldr f z r)) m)) l

  Eq-Tree : {{Eq a}} -> Eq (Tree a)
  Eq-Tree ._==_ t t' = toList t == toList t'

  Show-Tree : {{Show a}} -> Show (Tree a)
  Show-Tree .showsPrec _ Leaf = showString "Leaf"
  Show-Tree .showsPrec d (Two l x r) = showParen (d > appPrec)
    (showString "Two "
    <<< showsPrec appPrec+1 l
    <<< showString " "
    <<< showsPrec appPrec+1 x
    <<< showString " "
    <<< showsPrec appPrec+1 r)
  Show-Tree .showsPrec d (Three l x m y r) = showParen (d > appPrec)
    (showString "Three "
    <<< showsPrec appPrec+1 l
    <<< showString " "
    <<< showsPrec appPrec+1 x
    <<< showString " "
    <<< showsPrec appPrec+1 m
    <<< showString " "
    <<< showsPrec appPrec+1 y
    <<< showString " "
    <<< showsPrec appPrec+1 r)

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Tree a
empty = Leaf

singleton : a -> Tree a
singleton x = Two Leaf x Leaf

-------------------------------------------------------------------------------
-- Helpers for inserting and deleting
-------------------------------------------------------------------------------

private
  data TreeContext (a : Type) : Type where
    TwoLeft : a -> Tree a -> TreeContext a
    TwoRight : Tree a -> a -> TreeContext a
    ThreeLeft : a -> Tree a -> a -> Tree a -> TreeContext a
    ThreeMiddle : Tree a -> a -> a -> Tree a -> TreeContext a
    ThreeRight : Tree a -> a -> Tree a -> a -> TreeContext a

  data KickUp (a : Type) : Type where
    KickUp: : Tree a -> a -> Tree a -> KickUp a

  fromZipper : List (TreeContext a) -> Tree a -> Tree a
  fromZipper [] t = t
  fromZipper (h :: ctx) t =
    case h of \ where
      (TwoLeft x r) -> fromZipper ctx (Two t x r)
      (TwoRight l x) -> fromZipper ctx (Two l x t)
      (ThreeLeft x m y r) -> fromZipper ctx (Three t x m y r)
      (ThreeMiddle l x y r) -> fromZipper ctx (Three l x t y r)
      (ThreeRight l x m y) -> fromZipper ctx (Three l x m y t)

-------------------------------------------------------------------------------
-- Inserting
-------------------------------------------------------------------------------

insert : {{Ord a}} -> a -> Tree a -> Tree a
insert {a} v = down []
  where
    up : List (TreeContext a) -> KickUp a -> Tree a
    up [] (KickUp: l x r) = Two l x r
    up (h :: ctx) kup =
      case (h , kup) of \ where
        (TwoLeft x r , KickUp: l w m) ->
          fromZipper ctx (Three l w m x r)
        (TwoRight l x , KickUp: m w r) ->
          fromZipper ctx (Three l x m w r)
        (ThreeLeft x c y d , KickUp: a w b) ->
          up ctx (KickUp: (Two a w b) x (Two c y d))
        (ThreeMiddle a x y d , KickUp: b w c) ->
          up ctx (KickUp: (Two a x b) w (Two c y d))
        (ThreeRight a x b y , KickUp: c w d) ->
          up ctx (KickUp: (Two a x b) y (Two c w d))

    down : List (TreeContext a) -> Tree a -> Tree a
    down ctx Leaf = up ctx (KickUp: Leaf v Leaf)
    down ctx (Two l x r) =
      case compare v x of \ where
        EQ -> fromZipper ctx (Two l v r)
        LT -> down (TwoLeft x r :: ctx) l
        GT -> down (TwoRight l x :: ctx) r
    down ctx (Three l x m y r) =
      case (compare v x , compare v y) of \ where
        (EQ , _) -> fromZipper ctx (Three l v m y r)
        (_ , EQ) -> fromZipper ctx (Three l x m v r)
        (LT , _) -> down (ThreeLeft x m y r :: ctx) l
        (GT , LT) -> down (ThreeMiddle l x y r :: ctx) m
        (_ , _) -> down (ThreeRight l x m y :: ctx) r

-------------------------------------------------------------------------------
-- Deleting
-------------------------------------------------------------------------------

pop : {{Ord a}} -> a -> Tree a -> Maybe (Pair a (Tree a))
pop {a} v = down []
  where
    up : List (TreeContext a) -> Tree a -> Tree a
    up [] t = t
    up (h :: ctx) t =
      case (h , t) of \ where
        (TwoLeft x Leaf , Leaf) ->
          fromZipper ctx (Two Leaf x Leaf)
        (TwoRight Leaf x , Leaf) ->
          fromZipper ctx (Two Leaf x Leaf)
        (TwoLeft x (Two m y r) , l) ->
          up ctx (Three l x m y r)
        (TwoRight (Two l x m) y , r) ->
          up ctx (Three l x m y r)
        (TwoLeft x (Three b y c z d) , a) ->
          fromZipper ctx (Two (Two a x b) y (Two c z d))
        (TwoRight (Three a x b y c) z , d) ->
          fromZipper ctx (Two (Two a x b) y (Two c z d))
        (ThreeLeft x Leaf y Leaf , Leaf) ->
          fromZipper ctx (Three Leaf x Leaf y Leaf)
        (ThreeMiddle Leaf x y Leaf , Leaf) ->
          fromZipper ctx (Three Leaf x Leaf y Leaf)
        (ThreeRight Leaf x Leaf y , Leaf) ->
          fromZipper ctx (Three Leaf x Leaf y Leaf)
        (ThreeLeft x (Two b y c) z d , a) ->
          fromZipper ctx (Two (Three a x b y c) z d)
        (ThreeMiddle (Two a x b) y z d , c) ->
          fromZipper ctx (Two (Three a x b y c) z d)
        (ThreeMiddle a x y (Two c z d) , b) ->
          fromZipper ctx (Two a x (Three b y c z d))
        (ThreeRight a x (Two b y c) z , d) ->
          fromZipper ctx (Two a x (Three b y c z d))
        (ThreeLeft w (Three b x c y d) z e , a) ->
          fromZipper ctx (Three (Two a w b) x (Two c y d) z e)
        (ThreeMiddle (Three a w b x c) y z e , d) ->
          fromZipper ctx (Three (Two a w b) x (Two c y d) z e)
        (ThreeMiddle a w x (Three c y d z e) , b) ->
          fromZipper ctx (Three a w (Two b x c) y (Two d z e))
        (ThreeRight a w (Three b x c y d) z , e) ->
          fromZipper ctx (Three a w (Two b x c) y (Two d z e))
        (_ , _) -> t

    maxNode :  (t : Tree a) -> {{Validate Nonempty t}} -> a
    maxNode = \ where
      (Two _ x Leaf) -> x
      (Two _ _ r@(Two _ _ _)) -> maxNode r
      (Two _ _ r@(Three _ _ _ _ _)) -> maxNode r
      (Three _ _ _ x Leaf) -> x
      (Three _ _ _ _ r@(Two _ _ _)) -> maxNode r
      (Three _ _ _ _ r@(Three _ _ _ _ _)) -> maxNode r

    removeMaxNode : List (TreeContext a)
      -> (t : Tree a)
      -> {{Validate Nonempty t}}
      -> Tree a
    removeMaxNode ctx = \ where
      (Two Leaf _ Leaf) ->
        up ctx Leaf
      (Two l x r@(Two _ _ _)) ->
        removeMaxNode (TwoRight l x :: ctx) r
      (Two l x r@(Three _ _ _ _ _)) ->
        removeMaxNode (TwoRight l x :: ctx) r
      (Three Leaf x Leaf _ Leaf) ->
        up (TwoRight Leaf x :: ctx) Leaf
      (Three l x m y r@(Two _ _ _)) ->
        removeMaxNode (ThreeRight l x m y :: ctx) r
      (Three l x m y r@(Three _ _ _ _ _)) ->
        removeMaxNode (ThreeRight l x m y :: ctx) r
      t -> t

    down : List (TreeContext a) -> Tree a -> Maybe (Pair a (Tree a))
    down ctx Leaf = Nothing
    down ctx (Two l x r) =
      case (l , r , compare v x) of \ where
        (_ , Leaf , EQ) ->
          Just (x , up ctx Leaf)
        (l'@(Two _ _ _) , _ , EQ) ->
          Just (x , removeMaxNode (TwoLeft (maxNode l') r :: ctx) l')
        (l'@(Three _ _ _ _ _) , _ , EQ) ->
          Just (x , removeMaxNode (TwoLeft (maxNode l') r :: ctx) l')
        (_ , _ , LT) ->
          down (TwoLeft x r :: ctx) l
        (_ , _ , _ ) ->
          down (TwoRight l x :: ctx) r
    down ctx (Three l x m y r) =
      case (l , m , r , compare v x , compare v y) of \ where
        (Leaf , Leaf , Leaf , EQ , _) ->
          Just (x , fromZipper ctx (Two Leaf y Leaf))
        (Leaf , Leaf , Leaf , _ , EQ) ->
          Just (y , fromZipper ctx (Two Leaf x Leaf))
        (l'@(Two _ _ _) , _ , _ , EQ , _) ->
          Just (x , removeMaxNode (ThreeLeft (maxNode l') m y r :: ctx) l')
        (l'@(Three _ _ _ _ _) , _ , _ , EQ , _) ->
          Just (x , removeMaxNode (ThreeLeft (maxNode l') m y r :: ctx) l')
        (_ , m'@(Two _ _ _) , _ , _ , EQ) ->
          Just (x , removeMaxNode (ThreeMiddle l x (maxNode m') r :: ctx) m')
        (_ , m'@(Three _ _ _ _ _) , _ , _ , EQ) ->
          Just (x , removeMaxNode (ThreeMiddle l x (maxNode m') r :: ctx) m')
        (_ , _ , _ ,  LT , _) ->
          down (ThreeLeft x m y r :: ctx) l
        (_ , _ , _ ,  GT , LT) ->
          down (ThreeMiddle l x y r :: ctx) m
        (_ , _ , _ ,  _ , _ ) ->
          down (ThreeRight l x m y :: ctx) r

delete : {{Ord a}} -> a -> Tree a -> Tree a
delete x t = maybe t snd (pop x t)

-------------------------------------------------------------------------------
-- Querying
-------------------------------------------------------------------------------

lookup : {{Ord a}} -> a -> Tree (Pair a b) -> Maybe b
lookup a Leaf = Nothing
lookup a (Two l (x , b) r) =
  case compare a x of \ where
    EQ -> Just b
    LT -> lookup a l
    GT -> lookup a r
lookup a (Three l (x , b) m (y , c) r) =
  case (compare a x , compare a y) of \ where
    (EQ , _) -> Just b
    (LT , _) -> lookup a l
    (GT , EQ) -> Just c
    (GT , LT) -> lookup a m
    (GT , GT) -> lookup a r

member : {{Eq a}} -> a -> Tree a -> Bool
member a t = maybe False (const True) (find (_== a) t)

-------------------------------------------------------------------------------
--  Misc.
-------------------------------------------------------------------------------

fromList : {{Ord a}} -> List a -> Tree a
fromList xs = foldr insert Leaf xs

map : {{Ord b}} -> (a -> b) -> Tree a -> Tree b
map f = fromList <<< Prelude.map f <<< toList

mapMonotonic : (a -> b) -> Tree a -> Tree b
mapMonotonic {a} {b} f = go
  where
    go : Tree a -> Tree b
    go Leaf = Leaf
    go (Two l x r) = Two (go l) (f x) (go r)
    go (Three l x m y r) = Three (go l) (f x) (go m) (f y) (go r)

merge : {{Ord a}} -> Tree a -> Tree a -> Tree a
merge t t' = foldr insert t t'

filter : {{Ord a}} -> (a -> Bool) -> Tree a -> Tree a
filter p Leaf = Leaf
filter p (Two l x r) =
  let
    l' = filter p l
    r' = filter p r
  in
    if p x then Two l' x r' else merge l' r'
filter p (Three l x m y r) =
  let
    l' = filter p l
    m' = filter p m
    r' = filter p r
  in case (p x , p y) of \ where
    (False , False) -> merge (merge l' m') r'
    (True , True) -> Three l' x m' y r'
    (False , True) -> Two (merge l' m') y r'
    (True , False) -> Two l' x (merge m' r')
