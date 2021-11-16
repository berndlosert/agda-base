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
  Member0 : Member f (f :: fs)
  Member0 .inj x = here x
  Member0 .prj _ (here x) = just x
  Member0 .prj _ _ = nothing

  Member1 : Member f (f1 :: f :: fs)
  Member1 .inj x = there (here x)
  Member1 .prj _ (there (here x)) = just x
  Member1 .prj _ _ = nothing

  Member2 : Member f (f1 :: f2 :: f :: fs)
  Member2 .inj x = there (there (here x))
  Member2 .prj _ (there (there (here x))) = just x
  Member2 .prj _ _ = nothing

  Member3 : Member f (f1 :: f2 :: f3 :: f :: fs)
  Member3 .inj x = there (there (there (here x)))
  Member3 .prj _ (there (there (there (here x)))) = just x
  Member3 .prj _ _ = nothing

  Member4 : Member f (f1 :: f2 :: f3 :: f4 :: f :: fs)
  Member4 .inj x = there (there (there (there (here x))))
  Member4 .prj _ (there (there (there (there (here x))))) = just x
  Member4 .prj _ _ = nothing

  Member5 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f :: fs)
  Member5 .inj x = there (there (there (there (there (here x)))))
  Member5 .prj _ (there (there (there (there (there (here x)))))) = just x
  Member5 .prj _ _ = nothing

  Member6 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f :: fs)
  Member6 .inj x = there (there (there (there (there (there (here x))))))
  Member6 .prj _ (there (there (there (there (there (there (here x))))))) = just x
  Member6 .prj _ _ = nothing

  Member7 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f :: fs)
  Member7 .inj x = there (there (there (there (there (there (there (here x)))))))
  Member7 .prj _ (there (there (there (there (there (there (there (here x)))))))) = just x
  Member7 .prj _ _ = nothing

  Member8 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f :: fs)
  Member8 .inj x = there (there (there (there (there (there (there (there (here x))))))))
  Member8 .prj _ (there (there (there (there (there (there (there (there (here x))))))))) = just x
  Member8 .prj _ _ = nothing

  Member9 : Member f (f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f :: fs)
  Member9 .inj x = there (there (there (there (there (there (there (there (there (here x)))))))))
  Member9 .prj _ (there (there (there (there (there (there (there (there (there (here x)))))))))) = just x
  Member9 .prj _ _ = nothing
