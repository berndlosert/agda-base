module Data.Open.Sum1 where

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
-- Sum1
-------------------------------------------------------------------------------

data Sum1 : List (k -> Set) -> k -> Set where
  here :  f a -> Sum1 (f :: fs) a
  there : Sum1 fs a -> Sum1 (f :: fs) a

-------------------------------------------------------------------------------
-- Member
-------------------------------------------------------------------------------

record Member (f : k -> Set) (fs : List (k -> Set)) : Set where
  field
    inj : f a -> Sum1 fs a
    prj : (g : k -> Set) -> {{f === g}} -> Sum1 fs a -> Maybe (f a)

open Member {{...}} public

instance
  Member-0 : Member f (f :: fs)
  Member-0 .inj x = here x
  Member-0 .prj _ (here x) = just x
  Member-0 .prj _ _ = nothing

  Member-1 : Member f (f1 :: f :: fs)
  Member-1 .inj x = there (here x)
  Member-1 .prj _ (there (here x)) = just x
  Member-1 .prj _ _ = nothing

  Member-2 : Member f (f1 :: f2 :: f :: fs)
  Member-2 .inj x = there (there (here x))
  Member-2 .prj _ (there (there (here x))) = just x
  Member-2 .prj _ _ = nothing

  Member-3 : Member f (f1 :: f2 :: f3 :: f :: fs)
  Member-3 .inj x = there (there (there (here x)))
  Member-3 .prj _ (there (there (there (here x)))) = just x
  Member-3 .prj _ _ = nothing

  Member-4 : Member f (f1 :: f2 :: f3 :: f4 :: f :: fs)
  Member-4 .inj x = there (there (there (there (here x))))
  Member-4 .prj _ (there (there (there (there (here x))))) = just x
  Member-4 .prj _ _ = nothing

  Member-5 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f :: fs)
  Member-5 .inj x = there (there (there (there (there (here x)))))
  Member-5 .prj _ (there (there (there (there (there (here x)))))) = just x
  Member-5 .prj _ _ = nothing

  Member-6 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f :: fs)
  Member-6 .inj x = there (there (there (there (there (there (here x))))))
  Member-6 .prj _ (there (there (there (there (there (there (here x))))))) = just x
  Member-6 .prj _ _ = nothing

  Member-7 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f :: fs)
  Member-7 .inj x = there (there (there (there (there (there (there (here x)))))))
  Member-7 .prj _ (there (there (there (there (there (there (there (here x)))))))) = just x
  Member-7 .prj _ _ = nothing

  Member-8 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f :: fs)
  Member-8 .inj x = there (there (there (there (there (there (there (there (here x))))))))
  Member-8 .prj _ (there (there (there (there (there (there (there (there (here x))))))))) = just x
  Member-8 .prj _ _ = nothing

  Member-9 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f :: fs)
  Member-9 .inj x = there (there (there (there (there (there (there (there (there (here x)))))))))
  Member-9 .prj _ (there (there (there (there (there (there (there (there (there (here x)))))))))) = just x
  Member-9 .prj _ _ = nothing
