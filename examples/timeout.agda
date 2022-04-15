open import Prelude

open import Control.Concurrent
open import Control.Exception
open import System.IO
open import System.Time

main : IO Unit
main = do
  start <- getPOSIXTime
  res <- timeout 1_000_000 $ do
    x <- try (threadDelay 2_000_000)
    threadDelay 2_000_000
    pure x
  end <- getPOSIXTime
  putStrLn $ "Duration: " <> show (end - start)
  putStrLn $ "Result: " <> show (the (Maybe (Either SomeException Unit)) res)