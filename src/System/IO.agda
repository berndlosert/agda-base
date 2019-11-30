{-# OPTIONS --type-in-type #-}

module System.IO where

open import Agda.Builtin.IO public
open import Data.String
open import Data.Unit
open import Text.Show

postulate
  putStr : String → IO Unit
  putStrLn : String → IO Unit
  getLine : IO String
  getContents : IO String
  returnIO : {X : Set} → X → IO X
  bindIO : {X Y : Set} → IO X → (X → IO Y) → IO Y
  flushStdOut : IO Unit

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified System.IO as System #-}
{-# COMPILE GHC putStr = Text.putStr #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC getContents = Text.getContents #-}
{-# COMPILE GHC returnIO = \ _ a → return a #-}
{-# COMPILE GHC bindIO = \ _ _ ma f → ma >>= f #-}
{-# COMPILE GHC flushStdOut = System.hFlush System.stdout #-}

instance
  open import Control.Category
  open import Data.Functor
  Functor:IO : Endofunctor Sets IO
  Functor:IO .map f io = bindIO io (f >>> returnIO)

  open import Control.Monad
  Monad:IO : Monad Sets IO
  Monad:IO .join io = bindIO io id
  Monad:IO .return x = returnIO x

  open import Control.Applicative
  Applicative:IO = Idiom: ap return

  open import Data.Semigroup
  Semigroup:IO : {X : Set} {{_ : Semigroup X}} → Semigroup (IO X)
  Semigroup:IO = Semigroup: \ x y → liftA2 _<>_ x y

  open import Data.Monoid
  Monoid:IO : {X : Set} {{_ : Monoid X}} → Monoid (IO X)
  Monoid:IO = Monoid: (return mempty)

-- The print function outputs a value of any Show'able type to the
-- standard output device.
print : {X : Set} {{_ : Show X}} → X → IO Unit
print x = putStrLn (show x)

-- The interact function takes a function of type String → String
-- as its argument. The entire input from the standard input device is
-- passed to this function as its argument, and the resulting string is
-- output on the standard output device.
interact : (String → String) → IO Unit
interact f = do
  s <- getContents
  putStr (f s)
