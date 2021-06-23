{-# OPTIONS --type-in-type #-}

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

-- When using ST, you will need to compile with the option
--
--   --ghc-flag="-XImpredicativeTypes"
--
-- to prevent
--
--   GHC doesn't yet support impredicative polymorphism
--
-- errors.

postulate
  ST : Set -> Set -> Set
  runST : (forall {s} -> ST s a) -> a

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
-- ST FFI
-------------------------------------------------------------------------------


{-# FOREIGN GHC
  import Control.Monad.ST

  runST' :: () -> (forall s. () -> ST s a) -> a
  runST' _ f = runST (f ())
#-}

{-# COMPILE GHC ST = type ST #-}
{-# COMPILE GHC runST = runST' #-}
{-# COMPILE GHC mapST = \ _ _ _ -> fmap #-}
{-# COMPILE GHC pureST = \ _ _ -> return #-}
{-# COMPILE GHC apST = \ _ _ _ -> (<*>) #-}
{-# COMPILE GHC bindST = \ _ _ _ -> (>>=) #-}
