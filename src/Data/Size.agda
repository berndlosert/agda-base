{-# OPTIONS --type-in-type --sized-types #-}

module Data.Size where

-------------------------------------------------------------------------------
-- Size
-------------------------------------------------------------------------------

{-# BUILTIN SIZEUNIV SizeU #-}
{-# BUILTIN SIZE Size #-}
{-# BUILTIN SIZELT Size<_ #-}
{-# BUILTIN SIZESUC SizeSuc #-}
{-# BUILTIN SIZEINF Inf #-}
{-# BUILTIN SIZEMAX SizeMax #-}

{-# FOREIGN GHC
  type SizeLT i = ()
#-}

{-# COMPILE GHC Size = type () #-}
{-# COMPILE GHC Size<_ = type SizeLT #-}
{-# COMPILE GHC SizeSuc = \_ -> () #-}
{-# COMPILE GHC Inf = () #-}
{-# COMPILE GHC SizeMax = \_ _ -> () #-}

-------------------------------------------------------------------------------
-- Thunk
-------------------------------------------------------------------------------

record Thunk (i : Size) (f : Size -> Set) : Set where
  coinductive
  field force : {j : Size< i} -> f j

open Thunk public
