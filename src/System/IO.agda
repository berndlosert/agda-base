{-# OPTIONS --type-in-type #-}

module System.IO where

private variable A B : Set

module IO where
  open import Agda.Builtin.IO public
    using (IO)

  open import Data.String
  open import Data.String.Show

  open import Prelude
    hiding (map; pure)

  postulate
    map : (A -> B) -> IO A -> IO B
    pure : A -> IO A
    ap : IO (A -> B) -> IO A -> IO B
    bind : IO A -> (A -> IO B) -> IO B
    putStr : String -> IO Unit
    putStrLn : String -> IO Unit
    getLine : IO String
    getContents : IO String

  {-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
  {-# COMPILE GHC map = \ _ _ f io -> fmap f io #-}
  {-# COMPILE GHC pure = \ _ a -> pure a #-}
  {-# COMPILE GHC ap = \ _ _ f x -> f <*> x #-}
  {-# COMPILE GHC bind = \ _ _ io f -> io >>= f #-}
  {-# COMPILE GHC putStr = Text.putStr #-}
  {-# COMPILE GHC putStrLn = Text.putStrLn #-}
  {-# COMPILE GHC getLine = Text.getLine #-}
  {-# COMPILE GHC getContents = Text.getContents #-}

  print : {{_ : Show A}} -> A -> IO Unit
  print x = putStrLn (show x)

  interact : (String -> String) -> IO Unit
  interact f = bind getContents (\ s -> putStrLn (f s))

open IO public
  using (IO)

open import Prelude

instance
  functorIO : Functor IO
  functorIO .map = IO.map

  applicativeIO : Applicative IO
  applicativeIO .pure = IO.pure
  applicativeIO ._<*>_ = IO.ap

  monadIO : Monad IO
  monadIO ._>>=_ = IO.bind

  semigroupIO : {{_ : Semigroup A}} -> Semigroup (IO A)
  semigroupIO ._<>_ x y = (| _<>_ x y |)

  monoidIO : {{_ : Monoid A}} -> Monoid (IO A)
  monoidIO .mempty = return mempty
