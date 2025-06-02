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
    a b c : Type
    f m : Type -> Type

--------------------------------------------------------------------------------
-- Selective
-------------------------------------------------------------------------------

record Selective (f : Type -> Type) : Type where
  field
    overlap {{Applicative-super}} : Applicative f
    eitherS : f (a -> c) -> f (b -> c) -> f (Either a b) -> f c

  fromEitherS : f (Either a b) -> f (a -> b) -> f b
  fromEitherS x f = eitherS f (pure id) x

  infixr 0 ifS_then_else_
  ifS_then_else_ : f Bool -> f a -> f a -> f a
  ifS b then t else f = eitherS
    (| const f |)
    (| const t |)
    (| if b then pure (right tt) else pure (left tt) |)

  whenS : f Bool -> f Unit -> f Unit
  whenS b t = ifS b then t else (pure tt)

  fromMaybeS : f (Maybe a) -> f a -> f a
  fromMaybeS x y = fromEitherS (maybe (left tt) right <$> x) (const <$> y)

  infixr 0 _orElse_
  _orElse_ : {{Semigroup a}} -> f (Either a b) -> f (Either a b) -> f (Either a b)
  x orElse y = eitherS (flip appendLeft <$> y) (pure right) x
    where
      appendLeft : {{Semigroup a}} -> a -> Either a b -> Either a b
      appendLeft x (left y) = left (x <> y)
      appendLeft _ r = r

  infixr 0 _andAlso_
  _andAlso_ : {{Semigroup b}} -> f (Either a b) -> f (Either a b) -> f (Either a b)
  x andAlso y = mirror <$> ((mirror <$> x) orElse (mirror <$> y))

open Selective {{...}} public

whileS : {{Selective f}} -> f Bool -> f Unit
whileS act = whenS act (whileS act)

eitherM : {{Monad m}} -> m (a -> c) -> m (b -> c) -> m (Either a b) -> m c
eitherM f g m = caseM m \ where
  (left x) -> f <*> pure x
  (right x) -> g <*> pure x

--------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Selective-Function : Selective (Function a)
  Selective-Function .eitherS = eitherM

  Selective-Either : Selective (Either a)
  Selective-Either .eitherS = eitherM

  Selective-Tuple : {{Monoid a}} -> Selective (Tuple a)
  Selective-Tuple .eitherS = eitherM

  Selective-Maybe : Selective Maybe
  Selective-Maybe .eitherS = eitherM

  Selective-List : Selective List
  Selective-List .eitherS = eitherM

  Selective-IO : Selective IO
  Selective-IO .eitherS = eitherM
