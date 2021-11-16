module Data.Open.Product1 where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    k : Set
    a : k
    f f1 f2 f3 f4 f5 f6 f7 f8 f9 : k -> Set
    fs : List (k -> Set)

-------------------------------------------------------------------------------
-- Product1
-------------------------------------------------------------------------------

infixr 4 _:'_
data Product1 {k : Set} : List (k -> Set) -> k -> Set where
  [] : Product1 [] a
  _:'_ : f a -> Product1 fs a -> Product1 (f :: fs) a

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem {k : Set} (f : k -> Set) (fs : List (k -> Set)) : Set where
  field getElem : Product1 fs a -> f a

open Elem {{...}} public

instance
  Elem-0 : Elem f (f :: fs)
  Elem-0 .getElem (f :' _) = f

  Elem-1 : Elem f (f1 :: f :: fs)
  Elem-1 .getElem (_ :' f :' _) = f

  Elem-2 : Elem f (f1 :: f2 :: f :: fs)
  Elem-2 .getElem (_ :' _ :' f :' _) = f

  Elem-3 : Elem f (f1 :: f2 :: f3 :: f :: fs)
  Elem-3 .getElem (_ :' _ :' _ :' f :' _) = f

  Elem-4 : Elem f (f1 :: f2 :: f3 :: f4 :: f :: fs)
  Elem-4 .getElem (_ :' _ :' _ :' _ :' f :' _) = f

  Elem-5 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f :: fs)
  Elem-5 .getElem (_ :' _ :' _ :' _ :' _ :' f :' _) = f

  Elem-6 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f :: fs)
  Elem-6 .getElem (_ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Elem-7 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f :: fs)
  Elem-7 .getElem (_ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Elem-8 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f :: fs)
  Elem-8 .getElem (_ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Elem-9 : Elem f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f :: fs)
  Elem-9 .getElem (_ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f
