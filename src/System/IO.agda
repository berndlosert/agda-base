{-# OPTIONS --type-in-type #-}

module System.IO where

-- Import a bunch of IO functions from Haskell.

open import Agda.Builtin.IO public
open import Data.String.Base
open import Data.Unit

postulate
  putStr : String -> IO Unit
  putStrLn : String -> IO Unit
  getLine : IO String
  getContents : IO String
  returnIO : {X : Set} -> X -> IO X
  bindIO : {X Y : Set} -> IO X -> (X -> IO Y) -> IO Y
  flushStdOut : IO Unit

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified System.IO as System #-}
{-# COMPILE GHC putStr = Text.putStr #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC getContents = Text.getContents #-}
{-# COMPILE GHC returnIO = \ _ a -> return a #-}
{-# COMPILE GHC bindIO = \ _ _ ma f -> ma >>= f #-}
{-# COMPILE GHC flushStdOut = System.hFlush System.stdout #-}

-- IO forms a monad.

open import Control.Category
open import Control.Monad

instance
  Monad:IO : Monad Sets IO
  Monad:IO .return x = returnIO x
  Monad:IO .extend k io = bindIO io k

-- IO forms a functor.

open import Data.Functor

instance
  Functor:IO : Endofunctor Sets IO
  Functor:IO = Functor: liftM

-- IO is an applicative.

open import Control.Applicative

instance
  Applicative:IO = Idiom: ap return

-- IO X is a semigroup and a monoid whenever X is, respectively.

open import Data.Semigroup
open import Data.Monoid

instance
  Semigroup:IO : forall {X} {{_ : Semigroup X}} -> Semigroup (IO X)
  Semigroup:IO = Semigroup: \ x y -> map2 _<>_ x y

  Monoid:IO : forall {X} {{_ : Monoid X}} -> Monoid (IO X)
  Monoid:IO = Monoid: (return mempty)

-- The print function outputs a value of any Show'able type to the
-- standard output device.

open import Text.Show

print : forall {X} {{_ : Show X}} -> X -> IO Unit
print x = putStrLn (show x)

-- The interact function takes a function of type String -> String
-- as its argument. The entire input from the standard input device is
-- passed to this function as its argument, and the resulting string is
-- output on the standard output device.

interact : (String -> String) -> IO Unit
interact f = do
  s <- getContents
  putStr (f s)
