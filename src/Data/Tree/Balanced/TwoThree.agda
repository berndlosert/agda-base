{-# OPTIONS --type-in-type #-}

module Data.Tree.Balanced.TwoThree where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Constraint.Nonempty
open import Data.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

data Tree (a : Set) : Set where
  Leaf : Tree a
  Two : Tree a -> a -> Tree a -> Tree a
  Three : Tree a -> a -> Tree a -> a -> Tree a -> Tree a

instance
  NonemptyConstraint-Tree : NonemptyConstraint (Tree a)
  NonemptyConstraint-Tree .IsNonempty Leaf = Void
  NonemptyConstraint-Tree .IsNonempty _ = Unit

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
  data TreeContext (a : Set) : Set where
    TwoLeft : a -> Tree a -> TreeContext a
    TwoRight : Tree a -> a -> TreeContext a
    ThreeLeft : a -> Tree a -> a -> Tree a -> TreeContext a
    ThreeMiddle : Tree a -> a -> a -> Tree a -> TreeContext a
    ThreeRight : Tree a -> a -> Tree a -> a -> TreeContext a

  data KickUp (a : Set) : Set where
    KickUp: : Tree a -> a -> Tree a -> KickUp a

  fromZipper : List (TreeContext a) -> Tree a -> Tree a
  fromZipper [] t = t
  fromZipper (h :: ctx) t with h
  ... | TwoLeft x r = fromZipper ctx (Two t x r)
  ... | TwoRight l x = fromZipper ctx (Two l x t)
  ... | ThreeLeft x m y r = fromZipper ctx (Three t x m y r)
  ... | ThreeMiddle l x y r = fromZipper ctx (Three l x t y r)
  ... | ThreeRight l x m y = fromZipper ctx (Three l x m y t)

-------------------------------------------------------------------------------
-- Inserting
-------------------------------------------------------------------------------

insert : {{_ : Ord a}} -> a -> Tree a -> Tree a
insert {a} v = down []
  where
    up : List (TreeContext a) -> KickUp a -> Tree a
    up [] (KickUp: l x r) = Two l x r
    up (h :: ctx) kup with h | kup
    ... | TwoLeft x r | KickUp: l w m =
      fromZipper ctx (Three l w m x r)
    ... | TwoRight l x | KickUp: m w r =
      fromZipper ctx (Three l x m w r)
    ... | ThreeLeft x c y d | KickUp: a w b =
      up ctx (KickUp: (Two a w b) x (Two c y d))
    ... | ThreeMiddle a x y d | KickUp: b w c =
      up ctx (KickUp: (Two a x b) w (Two c y d))
    ... | ThreeRight a x b y | KickUp: c w d =
      up ctx (KickUp: (Two a x b) y (Two c w d))

    down : List (TreeContext a) -> Tree a -> Tree a
    down ctx Leaf = up ctx (KickUp: Leaf v Leaf)
    down ctx (Two l x r) with compare v x
    ... | EQ = fromZipper ctx (Two l v r)
    ... | LT = down (TwoLeft x r :: ctx) l
    ... | GT = down (TwoRight l x :: ctx) r
    down ctx (Three l x m y r)
      with compare v x | compare v y
    ... | EQ | _ = fromZipper ctx (Three l v m y r)
    ... | _ | EQ = fromZipper ctx (Three l x m v r)
    ... | LT | _ = down (ThreeLeft x m y r :: ctx) l
    ... | GT | LT = down (ThreeMiddle l x y r :: ctx) m
    ... | _ | _ = down (ThreeRight l x m y :: ctx) r

-------------------------------------------------------------------------------
-- Deleting
-------------------------------------------------------------------------------

pop : (a -> Ordering) -> Tree a -> Maybe (a * Tree a)
pop {a} p = down []
  where
    up : List (TreeContext a) -> Tree a -> Tree a
    up [] t = t
    up (h :: ctx) t with h | t
    ... | TwoLeft x Leaf | Leaf =
      fromZipper ctx (Two Leaf x Leaf)
    ... | TwoRight Leaf x | Leaf =
      fromZipper ctx (Two Leaf x Leaf)
    ... | TwoLeft x (Two m y r) | l =
      up ctx (Three l x m y r)
    ... | TwoRight (Two l x m) y | r =
      up ctx (Three l x m y r)
    ... | TwoLeft x (Three b y c z d) | a =
      fromZipper ctx (Two (Two a x b) y (Two c z d))
    ... | TwoRight (Three a x b y c) z | d =
      fromZipper ctx (Two (Two a x b) y (Two c z d))
    ... | ThreeLeft x Leaf y Leaf | Leaf =
      fromZipper ctx (Three Leaf x Leaf y Leaf)
    ... | ThreeMiddle Leaf x y Leaf | Leaf =
      fromZipper ctx (Three Leaf x Leaf y Leaf)
    ... | ThreeRight Leaf x Leaf y | Leaf =
      fromZipper ctx (Three Leaf x Leaf y Leaf)
    ... | ThreeLeft x (Two b y c) z d | a =
      fromZipper ctx (Two (Three a x b y c) z d)
    ... | ThreeMiddle (Two a x b) y z d | c =
      fromZipper ctx (Two (Three a x b y c) z d)
    ... | ThreeMiddle a x y (Two c z d) | b =
      fromZipper ctx (Two a x (Three b y c z d))
    ... | ThreeRight a x (Two b y c) z | d =
      fromZipper ctx (Two a x (Three b y c z d))
    ... | ThreeLeft w (Three b x c y d) z e | a =
      fromZipper ctx (Three (Two a w b) x (Two c y d) z e)
    ... | ThreeMiddle (Three a w b x c) y z e | d =
      fromZipper ctx (Three (Two a w b) x (Two c y d) z e)
    ... | ThreeMiddle a w x (Three c y d z e) | b =
      fromZipper ctx (Three a w (Two b x c) y (Two d z e))
    ... | ThreeRight a w (Three b x c y d) z | e =
      fromZipper ctx (Three a w (Two b x c) y (Two d z e))
    ... | _ | _ = t

    maxNode :  (t : Tree a) {{_ : IsNonempty t}} -> a
    maxNode t with t
    ... | Two _ x Leaf = x
    ... | Two _ _ r@(Two _ _ _) = maxNode r
    ... | Two _ _ r@(Three _ _ _ _ _) = maxNode r
    ... | Three _ _ _ x Leaf = x
    ... | Three _ _ _ _ r@(Two _ _ _) = maxNode r
    ... | Three _ _ _ _ r@(Three _ _ _ _ _) = maxNode r

    removeMaxNode : List (TreeContext a)
      -> (t : Tree a) {{_ : IsNonempty t}} -> Tree a
    removeMaxNode ctx t with t
    ... | Two Leaf _ Leaf =
      up ctx Leaf
    ... | Two l x r@(Two _ _ _) =
      removeMaxNode (TwoRight l x :: ctx) r
    ... | Two l x r@(Three _ _ _ _ _) =
      removeMaxNode (TwoRight l x :: ctx) r
    ... | Three Leaf x Leaf _ Leaf =
      up (TwoRight Leaf x :: ctx) Leaf
    ... | Three l x m y r@(Two _ _ _) =
      removeMaxNode (ThreeRight l x m y :: ctx) r
    ... | Three l x m y r@(Three _ _ _ _ _) =
      removeMaxNode (ThreeRight l x m y :: ctx) r
    ... | _ = t

    down : List (TreeContext a) -> Tree a -> Maybe (a * Tree a)
    down ctx Leaf = Nothing
    down ctx (Two l x r) with r | p x
    ... | Leaf | EQ = Just (x , up ctx Leaf)
    ... | _ | EQ = case l of \ where
      Leaf -> Nothing
      l'@(Two _ _ _) ->
        Just (x , removeMaxNode (TwoLeft (maxNode l') r :: ctx) l')
      l'@(Three _ _ _ _ _) ->
        Just (x , removeMaxNode (TwoLeft (maxNode l') r :: ctx) l')
    ... | _ | LT = down (TwoLeft x r :: ctx) l
    ... | _ | _  = down (TwoRight l x :: ctx) r
    down ctx (Three l x m y r) with l | m | r | p x | p y
    ... | Leaf | Leaf | Leaf | EQ | _  =
      Just (x , fromZipper ctx (Two Leaf y Leaf))
    ... | Leaf | Leaf | Leaf | _ | EQ =
      Just (y , fromZipper ctx (Two Leaf x Leaf))
    ... | _ | _ | _ | EQ | _ = case l of \ where
      Leaf -> Nothing
      l'@(Two _ _ _) ->
        Just (x , removeMaxNode (ThreeLeft (maxNode l') m y r :: ctx) l')
      l'@(Three _ _ _ _ _) ->
        Just (x , removeMaxNode (ThreeLeft (maxNode l') m y r :: ctx) l')
    ... | _ | _ | _ | _ | EQ = case m of \ where
      Leaf -> Nothing
      m'@(Two _ _ _) ->
        Just (x , removeMaxNode (ThreeMiddle l x (maxNode m') r :: ctx) m')
      m'@(Three _ _ _ _ _) ->
        Just (x , removeMaxNode (ThreeMiddle l x (maxNode m') r :: ctx) m')
    ... | _ | _ | _ |  LT | _  =
      down (ThreeLeft x m y r :: ctx) l
    ... | _ | _ | _ |  GT | LT =
      down (ThreeMiddle l x y r :: ctx) m
    ... | _ | _ | _ |  _ | _  =
      down (ThreeRight l x m y :: ctx) r

delete : (a -> Ordering) -> Tree a -> Tree a
delete p t = maybe t snd (pop p t)

-------------------------------------------------------------------------------
-- Querying
-------------------------------------------------------------------------------

lookup : (a -> Ordering) -> Tree a -> Maybe a
lookup p Leaf = Nothing
lookup p (Two l x r) with p x
... | EQ = Just x
... | LT = lookup p l
... | GT = lookup p r
lookup p (Three l x m y r) with p x | p y
... | EQ | _ = Just x
... | LT | _ = lookup p l
... | GT | EQ = Just y
... | GT | LT = lookup p m
... | GT | GT = lookup p r

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Tree : Foldable Tree
  Foldable-Tree .foldMap f t with t
  ... | Leaf =
    mempty
  ... | Two l x r =
    foldMap f l <> f x <> foldMap f r
  ... | Three l x m y r =
    foldMap f l <> f x <> foldMap f m <> f y <> foldMap f r

-------------------------------------------------------------------------------
--  Misc.
-------------------------------------------------------------------------------

fromList : {{_ : Ord a}} -> List a -> Tree a
fromList xs = foldr insert Leaf xs

map : {{_ : Ord b}} -> (a -> b) -> Tree a -> Tree b
map f = fromList <<< Prelude.map f <<< toList
