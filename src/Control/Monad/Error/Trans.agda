module Control.Monad.Error.Trans where

open import Prelude

private
  variable
    a b e e' : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- ErrorT
-------------------------------------------------------------------------------

record ErrorT (e : Set) (m : Set -> Set) (a : Set) : Set where
  constructor ErrorT:
  field runErrorT : m (e + a)

open ErrorT public

mapErrorT : (m (e + a) -> n (e' + b)) -> ErrorT e m a -> ErrorT e' n b
mapErrorT f m = ErrorT: $ f (runErrorT m)

instance
  Functor-ErrorT : {{_ : Functor m}} -> Functor (ErrorT e m)
  Functor-ErrorT .map f = ErrorT: ∘ map (map f) ∘ runErrorT

  Applicative-ErrorT : {{_ : Monad m}} -> Applicative (ErrorT e m)
  Applicative-ErrorT .pure x = ErrorT: $ return (Right x)
  Applicative-ErrorT ._<*>_ (ErrorT: mf) (ErrorT: mx) = ErrorT: do
    f <- mf
    case f of λ where
      (Left e) -> return $ Left e
      (Right g) -> do
        x <- mx
        case x of λ where
          (Left e) -> return $ Left e
          (Right y) -> return $ Right (g y)

  Monad-ErrorT : {{_ : Monad m}} -> Monad (ErrorT e m)
  Monad-ErrorT ._>>=_ (ErrorT: m) k = ErrorT: do
    x <- m
    case x of λ where
      (Left e) -> return $ Left e
      (Right y) -> runErrorT $ k y
