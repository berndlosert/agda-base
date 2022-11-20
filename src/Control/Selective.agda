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
  branch x l r = map (map left) x <*? map (map right) l <*? r

  eitherS : f (a -> c) -> f (b -> c) -> f (Either a b) -> f c
  eitherS l r x = branch x l r

  infixr 0 ifS_then_else_
  ifS_then_else_ : f Bool -> f a -> f a -> f a
  ifS b then t else f = branch
    (| if b then pure $ right tt else pure $ left tt |)
    (| const f |)
    (| const t |)

  whenS : f Bool -> f Unit -> f Unit
  whenS b t = ifS b then t else (pure tt)

  fromMaybeS : f a -> f (Maybe a) -> f a
  fromMaybeS x y = select (maybe (left tt) right <$> y) (const <$> x)

  infixr 9 _orElse_
  _orElse_ : {{Semigroup a}} -> f (Either a b) -> f (Either a b) -> f (Either a b)
  x orElse y = branch x (flip appendLeft <$> y) (pure right)
    where
      appendLeft : {{Semigroup a}} -> a -> Either a b -> Either a b
      appendLeft x (left y) = left (x <> y)
      appendLeft _ r = r

  infixr 9 _andAlso_
  _andAlso_ : {{Semigroup b}} -> f (Either a b) -> f (Either a b) -> f (Either a b)
  x andAlso y = mirror <$> (mirror <$> x) orElse (mirror <$> y)

open Selective {{...}} public

whileS : {{Selective f}} -> f Bool -> f Unit
whileS act = whenS act (whileS act)

selectM : {{Monad m}} -> m (Either a b) -> m (a -> b) -> m b
selectM m k = do
  res <- m
  case res of \ where
    (left x) -> do
      f <- k
      pure (f x)
    (right x) -> pure x

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

  Selective-IO : Selective IO
  Selective-IO .select = selectM
