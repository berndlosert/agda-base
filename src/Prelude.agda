{-# OPTIONS --type-in-type #-}

module Prelude where

open import Data.Function public using (_<<<_; _>>>_)
open import Data.Function public using (id; const; flip; _$_; Function)
open import Data.Boolean public using (Boolean; tt; ff; not; _&&_; _||_)
open import Data.Bool public using (Bool; true; false; if_then_else_)
open import Data.Void public using (Void)
open import Data.Unit public using (Unit; unit)
open import Data.Nat public using (Nat; suc)
open import Data.Int public using (Int; pos; negsuc)
open import Data.Float public using (Float)
open import Data.String public using (String)
open import Data.Char public using (Char)
open import Data.List public using (List; _::_; [])
open import Data.Maybe public using (Maybe; just; nothing)
open import Data.Either public using (Either; left; right)
open import Data.Pair public using (Pair; _,_; fst; snd)
open import Control.Applicative public using (Applicative; _<*>_; pure)
open import Control.Monad public using (Monad; _>>=_; return)
open import Data.Functor public using (Functor; map)
open import Data.String.Show using (Show; show)
open import System.IO using (IO)
