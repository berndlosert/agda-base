module Control.Monad.Instances where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad using (Monad; _>>=_)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Monad-Function : Monad (Function a)
  Monad-Function ._>>=_ f g x = g (f x) x

  Monad-Identity : Monad Identity
  Monad-Identity ._>>=_ x k = k (runIdentity x)

  Monad-Maybe : Monad Maybe
  Monad-Maybe ._>>=_ nothing _ = nothing
  Monad-Maybe ._>>=_ (just x) k = k x

  Monad-List : Monad List
  Monad-List ._>>=_ [] k = []
  Monad-List ._>>=_ (x :: xs) k = k x <> (xs >>= k)    
    
  Monad-Either : Monad (Either a)
  Monad-Either ._>>=_ (left x) _ = left x
  Monad-Either ._>>=_ (right x) k = k x

  Monad-Tuple : {{Monoid a}} -> Monad (Tuple a)
  Monad-Tuple ._>>=_ (u , x) k = let (v , y) = k x in (u <> v , y)