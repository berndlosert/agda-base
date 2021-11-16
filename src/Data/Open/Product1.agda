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
-- Member
-------------------------------------------------------------------------------

record Member {k : Set} (f : k -> Set) (fs : List (k -> Set)) : Set where
  field prj : Product1 fs a -> f a

open Member {{...}} public

instance
  Member-0 : Member f (f :: fs)
  Member-0 .prj (f :' _) = f

  Member-1 : Member f (f1 :: f :: fs)
  Member-1 .prj (_ :' f :' _) = f

  Member-2 : Member f (f1 :: f2 :: f :: fs)
  Member-2 .prj (_ :' _ :' f :' _) = f

  Member-3 : Member f (f1 :: f2 :: f3 :: f :: fs)
  Member-3 .prj (_ :' _ :' _ :' f :' _) = f

  Member-4 : Member f (f1 :: f2 :: f3 :: f4 :: f :: fs)
  Member-4 .prj (_ :' _ :' _ :' _ :' f :' _) = f

  Member-5 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f :: fs)
  Member-5 .prj (_ :' _ :' _ :' _ :' _ :' f :' _) = f

  Member-6 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f :: fs)
  Member-6 .prj (_ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Member-7 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f :: fs)
  Member-7 .prj (_ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Member-8 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f :: fs)
  Member-8 .prj (_ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f

  Member-9 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f :: fs)
  Member-9 .prj (_ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' _ :' f :' _) = f
