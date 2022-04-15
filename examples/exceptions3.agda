open import Prelude

open import Control.Concurrent
open import Control.Exception
open import System.IO

worker1 : IO Int
worker1 = do
  threadDelay 1
  putStrLn "initialzing"
  threadDelay 1
  putStrLn "doing some work..." 
  putStrLn "cleaning up"
  pure 1

worker2 : IO Int
worker2 = uninterruptibleMask \ restore -> do
  threadDelay 1
  putStrLn "initialzing"
  threadDelay 1
  putStrLn "doing some work..." 
  putStrLn "cleaning up"
  pure 1

worker3 : IO Unit
worker3 = do
  threadDelay 1 
  putStrLn "initialzing" catchAll (\ _ -> do
    threadDelay 1 catchAll (\ _ -> do
      putStrLn "doing some work..." 
      putStrLn "cleaning up"
      pure tt))

main1 = timeout 50 worker1 >>= print
main2 = timeout 1 worker2 >>= print
main3 = timeout 500 worker3 >>= print

main : IO Unit
main = main3
 