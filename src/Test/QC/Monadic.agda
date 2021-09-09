{-# OPTIONS --type-in-type --guardedness #-}

module Test.QC.Monadic where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Test.QC
open import Control.Monad.Cont.Trans
open import Control.Monad.IO.Class
open import Control.Monad.Trans.Class
open import String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- PropertyT
-------------------------------------------------------------------------------

abstract
  PropertyT : (Set -> Set) -> Set -> Set
  PropertyT m a = ContT (m Property) Gen a

  propertyT : ((a -> Gen (m Property)) -> Gen (m Property)) -> PropertyT m a
  propertyT = ContT:

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
  MonadTrans-PropertyT .lift m = propertyT (map (m >>=_) <<< promote)

  MonadIO-PropertyT : {{MonadIO m}} -> MonadIO (PropertyT m)
  MonadIO-PropertyT .liftIO = lift <<< liftIO

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

module _ {{_ : Monad m}} where

  run : m a -> PropertyT m a
  run = lift

  stop : {{Testable b}} -> b -> PropertyT m a
  stop b = propertyT \ _ -> pure $ pure $ property b

  pre : Bool -> PropertyT m Unit
  pre True  = pure tt
  pre False = stop tt

  assert : Bool -> PropertyT m Unit
  assert True = pure tt
  assert False = stop False

  monitor : (Property -> Property) -> PropertyT m Unit
  monitor f = propertyT \ k -> map f <$> k tt

  module _ {{_ : Show a}} where

    pick : Gen a -> PropertyT m a
    pick gen = propertyT \ k -> do
      a <- gen
      mp <- k a
      pure do
        p <- mp
        pure $ forAll (pure a) (const p)

    forAllM : Gen a -> (a -> PropertyT m b) -> PropertyT m b
    forAllM gen k = pick gen >>= k

  module _ {{_ : Testable a}} where

    monadic' : PropertyT m a -> Gen (m Property)
    monadic' m = unPropertyT m \ prop -> pure $ pure $ property prop

    monadic : (m Property -> Property) -> PropertyT m a -> Property
    monadic runner m = property (map runner (monadic' m))

monadicIO : {{Testable a}} -> PropertyT IO a -> Property
monadicIO = monadic ioProperty
