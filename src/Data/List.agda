{-# OPTIONS --type-in-type #-}

module Data.List where

open import Data.List.Base public

module List where
  open import Data.List.Api public
    hiding (
      Foldable:List;
      Traversable:List;
      Applicative:List;
      Monad:List
    )

open import Data.List.Api public
  using (
    Foldable:List;
    Traversable:List;
    Applicative:List;
    Monad:List
  )
