{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Effect where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

variable
  a : Set
  m : Set -> Set
  f g : (Set -> Set) -> Set
  fs : List ((Set -> Set) -> Set)

-------------------------------------------------------------------------------
-- Effect / Effects
-------------------------------------------------------------------------------

Effect : Set
Effect = (Set -> Set) -> Set

infixr 4 _:<_
data Effects (m : Set -> Set) : List Effect -> Set where
  Done : Effects m []
  _:<_ : f m -> Effects m fs -> Effects m (f :: fs)

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (f : Effect) (fs : List Effect) : Set where
  field getElem : Effects m fs -> f m

open Elem {{...}} public

instance
  Elem-Implies : {{Elem f fs}} -> Elem f (g :: fs)
  Elem-Implies .getElem (_ :< effs) = getElem effs

  Elem-Obvious : Elem f (f :: fs)
  Elem-Obvious .getElem (f :< _) = f

-------------------------------------------------------------------------------
-- Free (van Laarhoven)
-------------------------------------------------------------------------------

record Free (fs : List Effect) (a : Set) : Set where
  constructor Free:
  field runFree : {{Monad m}} -> Effects m fs -> m a

open Free public

instance
  Functor-Free : Functor (Free fs)
  Functor-Free .map f program = Free: (map f <<< runFree program)

  Applicative-Free : Applicative (Free fs)
  Applicative-Free .pure x = Free: (const $ pure x)
  Applicative-Free ._<*>_ fs xs =
    Free: \ effects -> runFree fs effects <*> runFree xs effects

  Monad-Free : Monad (Free fs)
  Monad-Free ._>>=_ program k =
    Free: \ effects -> runFree program effects >>= \ x -> runFree (k x) effects

-- Because Elem-Implies and Elem-Obvious overlap, interpreting will not
-- work without Agda complaining.
interpret : {{Monad m}} -> Effects m fs -> Free fs a -> m a
interpret interpreter program = runFree program interpreter

liftFree : {{Elem f fs}} -> (forall {m} -> f m -> m a) -> Free fs a
liftFree getOp = Free: \ effects -> getOp (getElem effects)

postulate
  Response : Set -> Set
  ByteString : Set
  RequestBody : Set

Url = String

record Http (m : Set -> Set) : Set where
  constructor Http:
  field
    getHttpEff : Url -> m (Either Nat (Response ByteString))
    postHttpEff : Url -> RequestBody -> m (Either Nat (Response ByteString))

open Http

record Logging (m : Set -> Set) : Set where
  constructor Logging:
  field logEff : String -> m Unit

open Logging

record Random (m : Set -> Set) : Set where
  constructor Random:
  field getRandEff : m Nat

open Random

record Suspend (m : Set -> Set) : Set where
  constructor Suspend:
  field suspendEff : Nat -> m Unit

open Suspend

getHttp : {{Elem Http fs}}
  -> Url -> Free fs (Either Nat (Response ByteString))
getHttp url = liftFree \ effect -> getHttpEff effect url

postHttp : {{Elem Http fs}}
  -> Url -> RequestBody -> Free fs (Either Nat (Response ByteString))
postHttp url body = liftFree \ effect -> postHttpEff effect url body

logMsg : {{Elem Logging fs}} -> String -> Free fs Unit
logMsg msg = liftFree \ effect -> logEff effect msg

getRand : {{Elem Random fs}} -> Free fs Nat
getRand = liftFree getRandEff

suspend : {{Elem Suspend fs}} -> Nat -> Free fs Unit
suspend n = liftFree \ effect -> suspendEff effect n

repeatReq : {{Elem Http fs}} -> {{Elem Random fs}} -> {{Elem Suspend fs}}
 -> Url -> Free fs (Either Nat (Response ByteString))
repeatReq {fs} url = do
    rand <- getRand
    let numRetries = rem rand 10
    eResponse <- getHttp url
    go numRetries eResponse
  where
    go : Nat -> Either Nat (Response ByteString) -> Free fs (Either Nat (Response ByteString))
    go 0 r = pure r
    go (Suc n) _ = do
      eResponse <- getHttp url
      case eResponse of \ where
        r@(Right _) -> pure r
        l@(Left _) -> suspend 100 >> go n eResponse

withLog : {{Elem Logging fs}} -> String -> String -> Free fs a -> Free fs a
withLog preMsg postMsg program = do
  logMsg preMsg
  a <- program
  logMsg postMsg
  pure a

program : {{Elem Http fs}}
  -> {{Elem Random fs}}
  -> {{Elem Suspend fs}}
  -> {{Elem Logging fs}}
  -> Free fs (Either Nat (Response ByteString))
program = withLog "running request!" "done!" (repeatReq "http://aaronlevin.ca")

postulate
  HttpException : Set
  handleExcep : HttpException -> Either Nat a
  httpIO : Http IO
  logIO : Logging IO
  randIO : Random IO
  suspendIO : Suspend IO

ioInterpreter : Effects IO (Http :: Logging :: Random :: Suspend :: [])
ioInterpreter = httpIO :< logIO :< randIO :< suspendIO :< Done

main : IO (Either Nat (Response ByteString))
main = interpret ioInterpreter program
