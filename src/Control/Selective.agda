{-# OPTIONS --type-in-type #-}

module Control.Selective where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    f m : Set -> Set

--------------------------------------------------------------------------------
-- Selective
-------------------------------------------------------------------------------

record Selective (f : Set -> Set) : Set where
  field
    overlap {{Applicative-super}} : Applicative f
    select : f (Either a b) -> f (a -> b) -> f b

  infixl 4 _<*?_
  _<*?_ : f (Either a b) -> f (a -> b) -> f b
  _<*?_ = select

  branch : f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
  branch x l r = map (map Left) x <*? map (map Right) l <*? r

  ifS : f Bool -> f a -> f a -> f a
  ifS x t f = branch
    (bool (Left unit) (Right unit) <$> x)
    (const <$> f)
    (const <$> t)

  whenS : f Bool -> f Unit -> f Unit
  whenS b t = ifS b t (pure unit)

  orElse : {{Semigroup a}} -> f (Either a b) -> f (Either a b) -> f (Either a b)
  orElse x y = branch x (flip appendLeft <$> y) (pure Right)
    where
      appendLeft : {{Semigroup a}} -> a -> Either a b -> Either a b
      appendLeft x (Left y) = Left (x <> y)
      appendLeft _ r = r

open Selective {{...}} public

{-# NON_TERMINATING #-}
whileS : {{Selective f}} -> f Bool -> f Unit
whileS act = whenS act (whileS act)

selectM : {{Monad m}} -> m (Either a b) -> m (a -> b) -> m b
selectM mx mf = do
  result <- mx
  case result of \ where
    (Left x) -> do
      f <- mf
      pure (f x)
    (Right x) -> pure x

--------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Selective-Function : Selective (Function a)
  Selective-Function .select = selectM

  Selective-Either : Selective (Either a)
  Selective-Either .select = selectM

  Selective-Pair : {{Monoid a}} -> Selective (Pair a)
  Selective-Pair .select = selectM

  Selective-Maybe : Selective Maybe
  Selective-Maybe .select = selectM

  Selective-List : Selective List
  Selective-List .select = selectM
