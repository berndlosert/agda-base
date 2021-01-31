{-# OPTIONS --type-in-type #-}

module Test.QC.Monadic where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Test.QC
open import Control.Monad.Cont.Trans
open import Control.Monad.IO.Class
open import Control.Monad.Trans.Class
open import System.IO.Unsafe

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b prop : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- PropertyT
-------------------------------------------------------------------------------

abstract
  PropertyT : (Set -> Set) -> Set -> Set
  PropertyT m a = ContT (m Property) Gen a

  PropertyT: : ((a -> Gen (m Property)) -> Gen (m Property)) -> PropertyT m a
  PropertyT: = ContT:

  unPropertyT : PropertyT m a -> (a -> Gen (m Property)) -> Gen (m Property)
  unPropertyT = runContT


-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

  instance
    Functor-PropertyT : Functor (PropertyT m)
    Functor-PropertyT = Functor-ContT

    Applicative-PropertyT : Applicative (PropertyT m)
    Applicative-PropertyT = Applicative-ContT

    Monad-PropertyT : Monad (PropertyT m)
    Monad-PropertyT = Monad-ContT

instance
  MonadTrans-PropertyT : MonadTrans PropertyT
  MonadTrans-PropertyT .lift m = PropertyT: (map (m >>=_) <<< promote)

  MonadIO-PropertyT : {{_ : MonadIO m}} -> MonadIO (PropertyT m)
  MonadIO-PropertyT .liftIO = lift <<< liftIO

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

monadicIO : PropertyT IO a -> Property
monadicIO m = property $ unsafePerformIO <$>
  (unPropertyT m $ const $ return $ return $ property True)

module _ {{_ : Monad m}} where

  run : m a -> PropertyT m a
  run = lift

  stop : {{_ : Testable prop}} -> prop -> PropertyT m a
  stop p = PropertyT: \ _ -> return (return (property p))

  pre : Bool -> PropertyT m Unit
  pre True  = return unit
  pre False = stop unit

  assert : Bool -> PropertyT m Unit
  assert True = return unit
  assert False = stop False

  monitor : (Property -> Property) -> PropertyT m Unit
  monitor f = PropertyT: \ k -> map f <$> k unit

  module _ {{_ : Testable a}} where

    monadic' : PropertyT m a -> Gen (m Property)
    monadic' m = unPropertyT m \ prop -> return $ return $ property prop

    monadic : (m Property -> Property) -> PropertyT m a -> Property
    monadic runner m = property (map runner (monadic' m))

  module _ {{_ : Show a}} where

    pick : Gen a -> PropertyT m a
    pick gen = PropertyT: \ k -> do
      a <- gen
      mp <- k a
      return $ do
        p <- mp
        return $ forAll (return a) (const p)

    forAllM : Gen a -> (a -> PropertyT m b) -> PropertyT m b
    forAllM gen k = pick gen >>= k
