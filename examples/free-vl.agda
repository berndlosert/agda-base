-- https://aaronlevin.ca/post/136494428283/extensible-effect-stacks-in-the-van-laarhoven-free

open import Prelude

open import Data.Bytes
open import Control.Concurrent
open import Control.Exception
open import Control.Monad.Free.VL
open import System.IO
open import System.Random as R using ()

variable
  a : Set
  fs : List Effect

Url : Set
Url = String

postulate
  RequestBody : Set
  Response : Set -> Set
  HttpException : Set
  instance Exception-HttpException : Exception HttpException
  get : Url -> IO (Response Bytes)
  post : Url -> RequestBody -> IO (Response Bytes)

record Http (m : Set -> Set) : Set where
  field
    getHttpEff : Url -> m (Either Nat (Response Bytes))
    postHttpEff : Url -> RequestBody -> m (Either Nat (Response Bytes))

open Http

record Logging (m : Set -> Set) : Set where
  field
     logEff : String -> m Unit

open Logging

record Random (m : Set -> Set) : Set where
  field
    getRandEff : m Nat

open Random

record Suspend (m : Set -> Set) : Set where
  field
    suspendEff : Nat -> m Unit

open Suspend

getHttp : {{Elem Http fs}}
  -> Url -> Free fs (Either Nat (Response Bytes))
getHttp url = liftFree (flip getHttpEff url)

postHttp : {{Elem Http fs}}
  -> Url -> RequestBody -> Free fs (Either Nat (Response Bytes))
postHttp url body = liftFree (\ http -> postHttpEff http url body)

logMsg : {{Elem Logging fs}}
  -> String -> Free fs Unit
logMsg msg = liftFree (flip logEff msg)

getRand : {{Elem Random fs}} -> Free fs Nat
getRand = liftFree getRandEff

suspend : {{Elem Suspend fs}} -> Nat -> Free fs Unit
suspend i = liftFree (flip suspendEff i)

repeatReq : {{Elem Http fs}} -> {{Elem Random fs}} -> {{Elem Suspend fs}}
  -> Url -> Free fs (Either Nat (Response Bytes))
repeatReq url = do
    numRetries <- getRand
    eResponse <- getHttp url
    go numRetries eResponse
  where
    go : Nat -> _ -> _
    go 0 r = pure r
    go (suc i) _ = do
        eResponse <- getHttp url
        case eResponse of \ where
            r@(right _) -> pure r
            l@(left _) -> suspend 100 >> go i eResponse

withLog : {{Elem Logging fs}}
  -> String -> String -> Free fs a -> Free fs a
withLog preMsg postMsg program = do
  logMsg preMsg
  a <- program
  logMsg postMsg
  pure a

program : {{Elem Http fs}} -> {{Elem Random fs}} -> {{Elem Suspend fs}} -> {{Elem Logging fs}}
  -> Free fs (Either Nat (Response Bytes))
program = withLog "running request!" "done!" (repeatReq "http://aaronlevin.ca")

handleExcep : HttpException -> Either Nat a
handleExcep _ = panic "unhandled HttpException"

httpIO : Http IO
httpIO = \ where
  .getHttpEff req -> catch (right <$> get req) (pure <<< handleExcep)
  .postHttpEff req body -> catch (right <$> post req body) (pure <<< handleExcep)

logIO : Logging IO
logIO = \ where
  .logEff -> putStrLn

randIO : Random IO
randIO = \ where
  .getRandEff -> R.randomRIO (0 , 100)

suspendIO : Suspend IO
suspendIO = \ where
  .suspendEff -> threadDelay

ioInterpreter : Effects IO (Http :: Logging :: Random :: Suspend :: [])
ioInterpreter = httpIO :' logIO :' randIO :' suspendIO :' []

main : IO Unit
main = interpret ioInterpreter program >> putStrLn "exit!"
