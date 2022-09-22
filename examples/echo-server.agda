open import Prelude

open import Data.Bytes as Bytes using ()
open import Data.List as List using ()
open import Data.String.Encoding
open import Network.Socket
open import System.IO

runTCPEchoServer : IO Unit
runTCPEchoServer = do
  (serverAddr , _) <- getAddrInfo nothing (just "127.0.0.1") (just "7000")
  serverSocket <- socket (addrFamily serverAddr) sockStream defaultProtocol
  setSocketOption serverSocket reuseAddr 1
  bind serverSocket (addrAddress serverAddr)
  listen serverSocket 1
  (clientSocket , _) <- accept serverSocket
  print "Waiting for a message..."
  message <- recv clientSocket 1024
  unless (Bytes.null message) do
    print ("Received: " <> decodeUtf8 message)
    print "Echoing..."
    sendAll clientSocket message
  print "Closing..."
  close clientSocket
  close serverSocket

main : IO Unit
main = runTCPEchoServer
