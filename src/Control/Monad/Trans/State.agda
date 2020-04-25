{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.State where

open import Prelude

open import Control.Monad.Trans.Class
  using (MonadTrans; lift; transform)

private
  variable
    A B S : Set
    M N : Set -> Set

--------------------------------------------------------------------------------
-- MonadState
--------------------------------------------------------------------------------

record MonadState (S : Set) (M : Set -> Set) : Set where
  field
    {{monad}} : Monad M
    get : M S
    put : S -> M Unit

  state : (S -> A * S) -> M A
  state f = do
    s0 <- get
    let (a , s1) = f s0
    put s1
    return a

  modify : (S -> S) -> M Unit
  modify f = state $ (λ s -> (unit , f s))

  gets : (S -> A) -> M A
  gets f = do
    s <- get
    return (f s)

open MonadState {{...}} public

--------------------------------------------------------------------------------
-- StateT
--------------------------------------------------------------------------------

record StateT (S : Set) (M : Set -> Set) (A : Set) : Set where
  constructor aStateT
  field runStateT : S -> M (A * S)

open StateT public

evalStateT : {{_ : Monad M}} -> StateT S M A -> S -> M A
evalStateT m s = do
  (a , _) <- runStateT m s
  return a

execStateT : {{_ : Monad M}} -> StateT S M A -> S -> M S
execStateT m s0 = do
  (_ , s1) <- runStateT m s0
  return s1

mapStateT : (M (A * S) -> N (B * S)) -> StateT S M A -> StateT S N B
mapStateT f m = aStateT $ f ∘ runStateT m

withStateT : (S -> S) -> StateT S M A -> StateT S M A
withStateT f m = aStateT $ runStateT m ∘ f

instance
  functorStateT : {{_ : Functor M}} -> Functor (StateT S M)
  functorStateT .map f m = aStateT $ λ s0 ->
    map (first f) $ runStateT m s0

  applicativeStateT : {{_ : Monad M}} -> Applicative (StateT S M)
  applicativeStateT = λ where
    .pure a -> aStateT $ λ s -> return (a , s)
    ._<*>_ mf mx -> aStateT $ λ s0 -> do
      (f , s1) <- runStateT mf s0
      (x , s2) <- runStateT mx s1
      return (f x , s2)

  alternativeStateT : {{_ : Alternative M}} {{_ : Monad M}} ->
    Alternative (StateT S M)
  alternativeStateT .empty = aStateT (const empty)
  alternativeStateT ._<|>_ m n = aStateT $ λ s ->
    runStateT m s <|> runStateT n s

  monadStateT : {{_ : Monad M}} -> Monad (StateT S M)
  monadStateT ._>>=_ m k = aStateT $ λ s0 -> do
    (a , s1) <- runStateT m s0
    runStateT (k a) s1

  monadTransStateT : MonadTrans (StateT S)
  monadTransStateT = λ where
    .lift m -> aStateT λ s -> do
      a <- m
      return (a , s)
    .transform -> monadStateT

  monadStateStateT : {{_ : Monad M}} -> MonadState S (StateT S M)
  monadStateStateT .get = aStateT $ return ∘ dupe
  monadStateStateT .put s = aStateT $ const $ return (unit , s)

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------

State : Set -> Set -> Set
State S = StateT S Identity

aState : (S -> A * S) -> State S A
aState t = aStateT (anIdentity ∘ t)

runState : State S A -> S -> A * S
runState m = runIdentity ∘ runStateT m

evalState : State S A -> S -> A
evalState m s = fst (runState m s)

execState : State S A -> S -> S
execState m s = snd (runState m s)

mapState : (A * S -> B * S) -> State S A -> State S B
mapState = mapStateT ∘ map

withState : (S -> S) -> State S ~> State S
withState f = withStateT f
