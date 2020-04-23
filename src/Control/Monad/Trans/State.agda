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
  modify f = state $ (\ s -> (unit , f s))

  gets : (S -> A) -> M A
  gets f = do
    s <- get
    return (f s)

open MonadState {{...}} public

--------------------------------------------------------------------------------
-- StateT
--------------------------------------------------------------------------------

record StateT (S : Set) (M : Set -> Set) (A : Set) : Set where
  constructor toStateT
  field fromStateT : S -> M (A * S)

open StateT public

evalStateT : {{_ : Monad M}} -> StateT S M A -> S -> M A
evalStateT m s = do
  (a , _) <- fromStateT m s
  return a

execStateT : {{_ : Monad M}} -> StateT S M A -> S -> M S
execStateT m s0 = do
  (_ , s1) <- fromStateT m s0
  return s1

mapStateT : (M (A * S) -> N (B * S)) -> StateT S M A -> StateT S N B
mapStateT f m = toStateT $ f <<< fromStateT m

withStateT : (S -> S) -> StateT S M A -> StateT S M A
withStateT f m = toStateT $ fromStateT m <<< f

instance
  functorStateT : {{_ : Functor M}} -> Functor (StateT S M)
  functorStateT .map f m = toStateT $ \ s0 ->
    map (first f) $ fromStateT m s0

  applicativeStateT : {{_ : Monad M}} -> Applicative (StateT S M)
  applicativeStateT = \ where
    .pure a -> toStateT $ \ s -> return (a , s)
    ._<*>_ mf mx -> toStateT $ \ s0 -> do
      (f , s1) <- fromStateT mf s0
      (x , s2) <- fromStateT mx s1
      return (f x , s2)

  alternativeStateT : {{_ : Alternative M}} {{_ : Monad M}} ->
    Alternative (StateT S M)
  alternativeStateT .empty = toStateT (const empty)
  alternativeStateT ._<|>_ m n = toStateT $ \ s ->
    fromStateT m s <|> fromStateT n s

  monadStateT : {{_ : Monad M}} -> Monad (StateT S M)
  monadStateT ._>>=_ m k = toStateT $ \ s0 -> do
    (a , s1) <- fromStateT m s0
    fromStateT (k a) s1

  monadTransStateT : MonadTrans (StateT S)
  monadTransStateT = \ where
    .lift m -> toStateT \ s -> do
      a <- m
      return (a , s)
    .transform -> monadStateT

  monadStateStateT : {{_ : Monad M}} -> MonadState S (StateT S M)
  monadStateStateT .get = toStateT $ return <<< dupe
  monadStateStateT .put s = toStateT $ const $ return (unit , s)

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------

State : Set -> Set -> Set
State S = StateT S Id

toState : (S -> A * S) -> State S A
toState t = toStateT (t >>> toId)

fromState : State S A -> S -> A * S
fromState m = fromId <<< fromStateT m

evalState : State S A -> S -> A
evalState m s = fst (fromState m s)

execState : State S A -> S -> S
execState m s = snd (fromState m s)

mapState : (A * S -> B * S) -> State S A -> State S B
mapState = mapStateT <<< map

withState : (S -> S) -> State S ~> State S
withState f = withStateT f
