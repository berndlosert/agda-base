{-# OPTIONS --type-in-type #-}

module Data.Tree.RBTree where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (join)

open import Data.Constraint.Nonempty

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- RBTree (types)
-------------------------------------------------------------------------------

data Color : Set where
  R B : Color

BlackHeight : Set
BlackHeight = Nat

data RBTree (a : Set) : Set where
  Leaf : RBTree a
  Node : Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a

instance
  Eq-Color : Eq Color
  Eq-Color ._==_ R R = True
  Eq-Color ._==_ B B = True
  Eq-Color ._==_ _ _ = False

  NonemptyConstraint-RBTree : NonemptyConstraint (RBTree a)
  NonemptyConstraint-RBTree .Nonempty Leaf = Void
  NonemptyConstraint-RBTree .Nonempty _ = Unit

-------------------------------------------------------------------------------
-- Basic functions
-------------------------------------------------------------------------------

height : RBTree a -> BlackHeight
height Leaf = 0
height (Node _ h _ _ _) = h

singleton : a -> RBTree a
singleton x = Node B 1 Leaf x Leaf

toList : RBTree a -> List a
toList t = inorder t []
  where
    inorder : RBTree a -> List a -> List a
    inorder Leaf xs = xs
    inorder (Node _ _ l x r) xs = inorder l (x :: inorder r xs)

member : {{_ : Ord a}} -> a -> RBTree a -> Bool
member _ Leaf = False
member x (Node _ _ l y r) with compare x y
... | LT = member x l
... | GT = member x r
... | EQ = True

minimum : (t : RBTree a) {{_ : Nonempty t}} -> a
minimum (Node _ _ Leaf x _) = x
minimum (Node _ _ l@(Node _ _ _ _ _) _ _) = minimum l

isRed : RBTree a -> Bool
isRed (Node R _ _ _ _ ) = True
isRed _ = False

-------------------------------------------------------------------------------
-- turn helpers
-------------------------------------------------------------------------------

turnR : (t : RBTree a) {{_ : Nonempty t}} -> RBTree a
turnR (Node _ h l x r) = Node R h l x r

turnB : (t : RBTree a) {{_ : Nonempty t}} -> RBTree a
turnB (Node _ h l x r) = Node B h l x r

turnB' : RBTree a -> RBTree a
turnB' Leaf = Leaf
turnB' (Node _ h l x r) = Node B h l x r

-------------------------------------------------------------------------------
-- balance helpers
-------------------------------------------------------------------------------

balanceL' : BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceL' h (Node R _ (Node R _ a x b) y c) z d =
    Node R (Suc h) (Node B h a x b) y (Node B h c z d)
balanceL' h (Node R _ a x (Node R _ b y c)) z d =
    Node R (Suc h) (Node B h a x b) y (Node B h c z d)
balanceL' h l x r = Node B h l x r

balanceR' : BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR' h a x (Node R _ b y (Node R _ c z d)) =
    Node R (Suc h) (Node B h a x b) y (Node B h c z d)
balanceR' h a x (Node R _ (Node R _ b y c) z d) =
    Node R (Suc h) (Node B h a x b) y (Node B h c z d)
balanceR' h l x r = Node B h l x r

balanceL : Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceL B h (Node R _ (Node R _ a x b) y c) z d =
    Node R (Suc h) (Node B h a x b) y (Node B h c z d)
balanceL B h (Node R _ a x (Node R _ b y c)) z d =
    Node R (Suc h) (Node B h a x b) y (Node B h c z d)
balanceL k h l x r = Node k h l x r

balanceR : Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR B h a x (Node R _ b y (Node R _ c z d)) =
    Node R (Suc h) (Node B h a x b) y (Node B h c z d)
balanceR B h a x (Node R _ (Node R _ b y c) z d) =
    Node R (Suc h) (Node B h a x b) y (Node B h c z d)
balanceR k h l x r = Node k h l x r

-------------------------------------------------------------------------------
-- Insertion
-------------------------------------------------------------------------------

insert' : {{_ : Ord a}} -> a -> RBTree a -> RBTree a
insert' kx Leaf = Node R 1 Leaf kx Leaf
insert' kx s@(Node B h l x r) with compare kx x
... | LT = balanceL' h (insert' kx l) x r
... | GT = balanceR' h l x (insert' kx r)
... | EQ = s
insert' kx s@(Node R h l x r) with compare kx x
... | LT = Node R h (insert' kx l) x r
... | GT = Node R h l x (insert' kx r)
... | EQ = s

insert : {{_ : Ord a}} -> a -> RBTree a -> RBTree a
insert kx t = turnB (insert' kx t) {{believeMe}}

-------------------------------------------------------------------------------
-- unbalanced helpers
-------------------------------------------------------------------------------

RBTreeBDel : Set -> Set
RBTreeBDel a = RBTree a * Bool

unbalancedL : Color -> BlackHeight -> RBTree a -> a -> RBTree a
  -> RBTreeBDel a
unbalancedL c h l@(Node B _ _ _ _) x r
  = (balanceL B h (turnR l) x r , c == B)
unbalancedL B h (Node R lh ll lx lr@(Node B _ _ _ _)) x r
  = (Node B lh ll lx (balanceL B h (turnR lr) x r), False)
unbalancedL _ _ _ _ _ = error "unbalancedL"

unbalancedR : Color -> BlackHeight -> RBTree a -> a -> RBTree a
  -> RBTree a * Bool
unbalancedR c h l x r@(Node B _ _ _ _)
  = (balanceR B h l x (turnR r) , c == B)
unbalancedR B h l x (Node R rh rl@(Node B _ _ _ _) rx rr)
  = (Node B rh (balanceR B h l x (turnR rl)) rx rr , False)
unbalancedR _ _ _ _ _ = error "unbalancedR"

-------------------------------------------------------------------------------
-- Deletion
-------------------------------------------------------------------------------

deleteMin' : (t : RBTree a) {{_ : Nonempty t}} -> RBTreeBDel a * a
deleteMin' (Node B _ Leaf x Leaf) = (Leaf , True , x)
deleteMin' (Node B _ Leaf x r@(Node R _ _ _ _)) = (turnB r , False , x)
deleteMin' (Node B _ Leaf x r@(Node B _ _ _ _)) = (r , False , x)
deleteMin' (Node R _ Leaf x r) = (r , False , x)
deleteMin' (Node c h l@(Node _ _ _ _ _) x r) =
  let
    (l' , d , m) = deleteMin' l
    tD  = unbalancedR c (h - 1) l' x r
    tD' = (Node c h l' x r , False)
  in
    if d then (tD , m) else (tD' , m)

deleteMin : RBTree a -> RBTree a
deleteMin Leaf = Leaf
deleteMin t@(Node _ _ _ _ _) = turnB' (fst (fst (deleteMin' t)))

blackify : RBTree a -> RBTreeBDel a
blackify s@(Node R _ _ _ _) = (turnB s , False)
blackify s = (s , True)

delete' : {{_ : Ord a}} -> a -> RBTree a -> RBTreeBDel a
delete' _ Leaf = (Leaf , False)
delete' x (Node c h l y r) with compare x y
... | LT =
  let
    (l' , d) = delete' x l
    t = Node c h l' y r
  in
    if d then unbalancedR c (h - 1) l' y r else (t , False)
... | GT =
  let
    (r' , d) = delete' x r
    t = Node c h l y r'
  in
    if d then unbalancedL c (h - 1) l y r' else (t , False)
... | EQ = case r of \ where
  Leaf -> if c == B then blackify l else (l , False)
  r@(Node _ _ _ _ _) ->
    let
      (r' , d , m) = deleteMin' r
      t = Node c h l m r'
    in
      if d then unbalancedL c (h - 1) l m r' else (t , False)

delete : {{_ : Ord a}} -> a -> RBTree a -> RBTree a
delete x t = turnB' (fst (delete' x t))

-------------------------------------------------------------------------------
-- Joining
-------------------------------------------------------------------------------

joinLT : {{_ : Ord a}}
  -> RBTree a -> a -> RBTree a -> BlackHeight -> RBTree a
joinLT t1 g t2@(Node c h l x r) h1 =
  if h == h1
    then Node R (Suc h) t1 g t2
    else balanceL c h (joinLT t1 g l h1) x r
joinLT _ _ _ _ = error "joinLT"

joinGT : {{_ : Ord a}}
  -> RBTree a -> a -> RBTree a -> BlackHeight -> RBTree a
joinGT t1@(Node c h l x r) g t2 h2 =
  if h == h2
    then Node R (Suc h) t1 g t2
    else balanceR c h l x (joinGT r g t2 h2)
joinGT _ _ _ _ = error "joinGT"

join : {{_ : Ord a}} -> RBTree a -> a -> RBTree a -> RBTree a
join Leaf g t2 = insert g t2
join t1 g Leaf = insert g t1
join t1 g t2 =
  let
    h1 = height t1
    h2 = height t2
  in case compare h1 h2 of \ where
    LT -> turnB (joinLT t1 g t2 h1) {{believeMe}}
    GT -> turnB (joinGT t1 g t2 h2) {{believeMe}}
    EQ -> Node B (Suc h1) t1 g t2

-------------------------------------------------------------------------------
-- Merging
-------------------------------------------------------------------------------

mergeEQ : {{_ : Ord a}} -> RBTree a -> RBTree a -> RBTree a
mergeEQ Leaf Leaf = Leaf
mergeEQ t1@(Node _ h l x r@(Node R _ rl rx rr)) t2 =
  let
    m  = minimum t2 {{believeMe}}
    t2' = deleteMin t2
    h2' = height t2'
  in
    if h == h2' then  Node R (Suc h) t1 m t2'
    else if isRed l then Node R (Suc h) (turnB l {{believeMe}}) x (Node B h r m t2')
    else if isRed r then Node B h (Node R h l x rl) rx (Node R h rr m t2')
    else Node B h (turnR t1) m t2'
mergeEQ _ _ = error "mergeEQ"

mergeLT : {{_ : Ord a}} -> RBTree a -> RBTree a -> BlackHeight -> RBTree a
mergeLT t1 t2@(Node c h l x r) h1 =
  if h == h1
    then mergeEQ t1 t2
    else  balanceL c h (mergeLT t1 l h1) x r
mergeLT _ _ _ = error "mergeLT"

mergeGT : {{_ : Ord a}} -> RBTree a -> RBTree a -> BlackHeight -> RBTree a
mergeGT t1@(Node c h l x r) t2 h2 =
  if h == h2
    then mergeEQ t1 t2
    else balanceR c h l x (mergeGT r t2 h2)
mergeGT _ _ _ = error "mergeGT"
