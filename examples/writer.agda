open import Prelude

open import Control.Monad.Codensity
open import Control.Monad.State
open import Control.Monad.Writer
open import Data.Enum
open import Data.Foldable
open import Data.Functor.Identity
open import Data.List
open import Data.Monoid.Sum
open import Data.Traversable
open import System.IO

variable
  a b w : Set
  f t : Set -> Set

record Writer' (w a : Set) : Set where
  constructor asWriter'
  field runWriter' : forall {b} -> (w -> a -> b) -> b

open Writer'

fst' : Writer' w a -> w
fst' (asWriter' p) = p \ w _ -> w

snd' : Writer' w a -> a
snd' (asWriter' p) = p \ _ a -> a

pair' : w -> a -> Writer' w a
pair' w a = asWriter' \ h -> h w a

instance
  Functor-Writer' : Functor (Writer' w)
  Functor-Writer' .map f p = pair' (fst' p) (f $ snd' p)

  Applicative-Writer' : {{Monoid w}} -> Applicative (Writer' w)
  Applicative-Writer' ._<*>_ pf px = pair' (fst' pf <> fst' px) (snd' pf $ snd' px)
  Applicative-Writer' .pure x = pair' mempty x

tell' : w -> Writer' w Unit
tell' w = pair' w tt

largerSample : Writer (Sum Nat) Unit
largerSample = replicateA* 10_000_000 (tell (asSum 1))

largerSample' : Writer' (Sum Nat) Unit
largerSample' = replicateA* 10_000_000 (tell' (asSum 1))

largerSample1 : Codensity (Writer (Sum Nat)) Unit
largerSample1 = replicateA* 10_000_000 $ liftCodensity (tell (asSum 1))

foldMap' : {{Traversable t}} -> {{Monoid b}} -> (a -> b) -> t a -> b
foldMap' f = foldl (\ acc a -> acc <> f a) mempty

replicateA' : {{Applicative f}} -> Nat -> f a -> f Unit
replicateA' n x = foldl (\ acc y -> acc seq (y *> acc)) x (replicate n x) *> pure tt

largerSample2 : Writer (Sum Nat) Unit
largerSample2 = replicateA' 10_000_000 (tell (asSum 1))

main : IO Unit
main = do
  --print (runWriter largerSample) -- 3.7GB 6.5s
  --print (runWriter $ lowerCodensity $ largerSample1) -- 3.3GB 6.5s
  --print (fst' $ largerSample') -- 2.5GB 5.8s
  --print (sum $ replicate 10_000_000 (the Nat 1)) -- 5MB 0.4s
  --print (foldMap asSum $ replicate 10_000_000 (the Nat 1)) -- 1GB 2.3s
  --print (foldMap' asSum $ replicate 10_000_000 (the Nat 1)) -- 5MB 0.4s
  print (runWriter largerSample2) -- 2.5GB 5.8s