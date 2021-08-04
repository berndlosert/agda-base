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
    a b s : Type

-------------------------------------------------------------------------------
-- ST
-------------------------------------------------------------------------------

postulate
  ST : Type -> Type -> Type
  -- N.B. Requires adding -XImpredicativeTypes to the --ghc-flag option when
  -- compiling. Otherwise, you will get impredicativity errors.
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
{-# COMPILE GHC pureST = \ _ _ -> pure #-}
{-# COMPILE GHC apST = \ _ _ _ -> (<*>) #-}
{-# COMPILE GHC bindST = \ _ _ _ -> (>>=) #-}
