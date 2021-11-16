-- https://aaronlevin.ca/post/136494428283/extensible-effect-stacks-in-the-van-laarhoven-free

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Bytes
open import Control.Concurrent
open import Control.Exception
open import Control.Monad.Free.VL
open import Data.Open.Product1
open import System.IO
open import System.Random as R using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

variable
  a : Set
  fs : List ((Set -> Set) -> Set)

Url : Set
Url = String

-------------------------------------------------------------------------------
-- Postulates
-------------------------------------------------------------------------------

postulate
  RequestBody : Set
  Response : Set -> Set
  HttpException : Set
  instance Exception-HttpException : Exception HttpException
  get : Url -> IO (Response Bytes)
  post : Url -> RequestBody -> IO (Response Bytes)

-------------------------------------------------------------------------------
-- Effects
-------------------------------------------------------------------------------

record Http (m : Set -> Set) : Set where
  field
    getHttpEff : Url -> m (Either Nat (Response Bytes))
    postHttpEff : Url -> RequestBody -> m (Either Nat (Response Bytes))

open Http

record Logging (m : Set -> Set) : Set where
  field logEff : String -> m Unit

open Logging

record Random (m : Set -> Set) : Set where
  field getRandEff : m Nat

open Random

record Suspend (m : Set -> Set) : Set where
  field suspendEff : Nat -> m Unit

open Suspend

-------------------------------------------------------------------------------
-- Smart constructors
-------------------------------------------------------------------------------

getHttp : {{Member Http fs}}
  -> Url -> Free (Product1 fs) (Either Nat (Response Bytes))
getHttp url = liftFree \ prod -> getHttpEff (prj prod) url

postHttp : {{Member Http fs}}
  -> Url -> RequestBody -> Free (Product1 fs) (Either Nat (Response Bytes))
postHttp url body = liftFree \ prod -> postHttpEff (prj prod) url body

logMsg : {{Member Logging fs}} -> String -> Free (Product1 fs) Unit
logMsg msg = liftFree \ prod -> logEff (prj prod) msg

getRand : {{Member Random fs}} -> Free (Product1 fs) Nat
getRand = liftFree \ prod -> getRandEff (prj prod)

suspend : {{Member Suspend fs}} -> Nat -> Free (Product1 fs) Unit
suspend n = liftFree \ prod -> suspendEff (prj prod) n

-------------------------------------------------------------------------------
-- Effect handlers
-------------------------------------------------------------------------------

handleExcep : HttpException -> Either Nat a
handleExcep _ = panic "unhandled HttpException"

httpIO : Http IO
httpIO .getHttpEff req = catch (right <$> get req) (pure <<< handleExcep)
httpIO .postHttpEff req body = catch (right <$> post req body) (pure <<< handleExcep)

logIO : Logging IO
logIO .logEff = putStrLn

randIO : Random IO
randIO .getRandEff = R.randomRIO (0 , 10)

suspendIO : Suspend IO
suspendIO .suspendEff = threadDelay

ioHandler : Product1 (Http :: Logging :: Random :: Suspend :: []) IO
ioHandler = httpIO :' logIO :' randIO :' suspendIO :' []

-------------------------------------------------------------------------------
-- Some programs
-------------------------------------------------------------------------------

repeatReq : {{Member Http fs}} -> {{Member Random fs}} -> {{Member Suspend fs}}
  -> Url -> Free (Product1 fs) (Either Nat (Response Bytes))
repeatReq url = do
    numRetries <- getRand
    eResponse <- getHttp url
    go numRetries eResponse
  where
    go : Nat -> _ -> _
    go 0 r = pure r
    go (suc n) _ = do
        eResponse <- getHttp url
        case eResponse of \ where
            r@(right _) -> pure r
            l@(left _) -> suspend 100 >> go n eResponse

withLog : {{Member Logging fs}}
  -> String -> String -> Free (Product1 fs) a -> Free (Product1 fs) a
withLog preMsg postMsg program = do
  logMsg preMsg
  a <- program
  logMsg postMsg
  pure a

program : {{Member Http fs}} -> {{Member Random fs}} -> {{Member Suspend fs}} -> {{Member Logging fs}}
  -> Free (Product1 fs) (Either Nat (Response Bytes))
program = withLog "running request!" "done!" (repeatReq "http://aaronlevin.ca")

-------------------------------------------------------------------------------
-- Interpreting the program
-------------------------------------------------------------------------------

main : IO Unit
main = interpret ioHandler program >> putStrLn "exit!"
