{-# OPTIONS --type-in-type #-}

module Data.List.Alternative where

open import Control.Alternative public
open import Data.List.Applicative
open import Data.List.Base

instance
  Alternative:List : Alternative List
  Alternative:List ._<|>_ = _++_
  Alternative:List .empty = []
