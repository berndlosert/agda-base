module Control.Monad.ST where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b s : Set

-------------------------------------------------------------------------------
-- ST
-------------------------------------------------------------------------------

postulate
  ST : Set -> Set -> Set

private
  postulate
    mapST : (a -> b) -> ST s a -> ST s b
    pureST : a -> ST s a
    apST : ST s (a -> b) -> ST s a -> ST s b
    bindST : ST s a -> (a -> ST s b) -> ST s b

instance
  Functor-ST : Functor (ST s)
  Functor-ST .map = mapST

  Applicative-ST : Applicative (ST s)
  Applicative-ST .pure = pureST
  Applicative-ST ._<*>_ = apST

  Monad-ST : Monad (ST s)
  Monad-ST ._>>=_ = bindST

-------------------------------------------------------------------------------
-- runST
-------------------------------------------------------------------------------

private
  -- This guy is needed to avoid impredicativity issues.
  record ST' (a : Set) : Set where
    constructor anST'
    field unST' : forall {s} -> ST s a

  open ST'
  
  postulate
    runST' : ST' a -> a

runST : (forall {s} -> ST s a) -> a
runST st = runST' (anST' st)

-------------------------------------------------------------------------------
-- ST FFI
-------------------------------------------------------------------------------


{-# FOREIGN GHC
  import Control.Monad.ST

  newtype ST' a = ST' (forall s. () -> ST s a)

  runST' :: () -> ST' a -> a
  runST' _ (ST' st) = runST (st ())
#-}

{-# COMPILE GHC ST = type ST #-}
{-# COMPILE GHC mapST = \ _ _ _ -> fmap #-}
{-# COMPILE GHC pureST = \ _ _ -> pure #-}
{-# COMPILE GHC apST = \ _ _ _ -> (<*>) #-}
{-# COMPILE GHC bindST = \ _ _ _ -> (>>=) #-}
{-# COMPILE GHC ST' = data ST' (ST') #-}
{-# COMPILE GHC runST' = runST' #-}
