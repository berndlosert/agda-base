module Data.Open.Sum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a a1 a2 a3 a4 a5 a6 a7 a8 a9 : Set
    as : List Set

-------------------------------------------------------------------------------
-- Sum
-------------------------------------------------------------------------------

data Sum : List Set -> Set where
  here : a -> Sum (a :: as)
  there : Sum as -> Sum (a :: as)

-------------------------------------------------------------------------------
-- Member
-------------------------------------------------------------------------------

record Member (a : Set) (as : List Set) : Set where
  field
    inj : a -> Sum as
    prj : (b : Set) -> {{a === b}} -> Sum as -> Maybe a

open Member {{...}} public

instance
  Member0 : Member a (a :: as)
  Member0 .inj x = here x
  Member0 .prj _ (here x) = just x
  Member0 .prj _ _ = nothing

  Member1 : Member a (a1 :: a :: as)
  Member1 .inj x = there (here x)
  Member1 .prj _ (there (here x)) = just x
  Member1 .prj _ _ = nothing

  Member2 : Member a (a1 :: a2 :: a :: as)
  Member2 .inj x = there (there (here x))
  Member2 .prj _ (there (there (here x))) = just x
  Member2 .prj _ _ = nothing

  Member3 : Member a (a1 :: a2 :: a3 :: a :: as)
  Member3 .inj x = there (there (there (here x)))
  Member3 .prj _ (there (there (there (here x)))) = just x
  Member3 .prj _ _ = nothing

  Member4 : Member a (a1 :: a2 :: a3 :: a4 :: a :: as)
  Member4 .inj x = there (there (there (there (here x))))
  Member4 .prj _ (there (there (there (there (here x))))) = just x
  Member4 .prj _ _ = nothing

  Member5 : Member a (a1 :: a2 :: a3 :: a4 :: a5 :: a :: as)
  Member5 .inj x = there (there (there (there (there (here x)))))
  Member5 .prj _ (there (there (there (there (there (here x)))))) = just x
  Member5 .prj _ _ = nothing

  Member6 : Member a (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a :: as)
  Member6 .inj x = there (there (there (there (there (there (here x))))))
  Member6 .prj _ (there (there (there (there (there (there (here x))))))) = just x
  Member6 .prj _ _ = nothing

  Member7 : Member a (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a :: as)
  Member7 .inj x = there (there (there (there (there (there (there (here x)))))))
  Member7 .prj _ (there (there (there (there (there (there (there (here x)))))))) = just x
  Member7 .prj _ _ = nothing

  Member8 : Member a (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a :: as)
  Member8 .inj x = there (there (there (there (there (there (there (there (here x))))))))
  Member8 .prj _ (there (there (there (there (there (there (there (there (here x))))))))) = just x
  Member8 .prj _ _ = nothing

  Member9 : Member a (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a :: as)
  Member9 .inj x = there (there (there (there (there (there (there (there (there (here x)))))))))
  Member9 .prj _ (there (there (there (there (there (there (there (there (there (here x)))))))))) = just x
  Member9 .prj _ _ = nothing
