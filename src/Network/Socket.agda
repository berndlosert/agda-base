module Network.Socket where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Bytes
open import Data.String.Show
open import Data.Word

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    r : Type

-------------------------------------------------------------------------------
-- ProtocolNumber, PortNumber, HostName, HostIPv4Addr, ServiceName
-------------------------------------------------------------------------------

postulate
  ProtocolNumber : Type
  defaultProtocol : ProtocolNumber

  PortNumber : Type
  defaultPort : PortNumber

HostName : Type
HostName = String

HostIPv4Addr : Type
HostIPv4Addr = Word32

ServiceName : Type
ServiceName = String

-------------------------------------------------------------------------------
-- SocketAddr
-------------------------------------------------------------------------------

postulate
  SocketAddr : Type
  SocketAddrIPv4 : PortNumber -> HostIPv4Addr -> SocketAddr

private
  postulate
    socketAddrShow : SocketAddr -> String

instance
  Show-SocketAddr : Show SocketAddr
  Show-SocketAddr .show = socketAddrShow
  Show-SocketAddr .showsPrec = showsPrecDefault

-------------------------------------------------------------------------------
-- SocketType
-------------------------------------------------------------------------------

postulate
  SocketType : Type
  sockNone : SocketType
  sockStream : SocketType

-------------------------------------------------------------------------------
-- AddrFamily
-------------------------------------------------------------------------------

postulate
  AddrFamily : Type
  afInet : AddrFamily
  afUnspec : AddrFamily

-------------------------------------------------------------------------------
-- AddrInfoFlag
-------------------------------------------------------------------------------

data AddrInfoFlag : Type where
  aiAddrConfig : AddrInfoFlag
  aiAll : AddrInfoFlag
  aiCanonName : AddrInfoFlag
  aiNumericHost : AddrInfoFlag
  aiNumericServ : AddrInfoFlag
  aiPassive : AddrInfoFlag
  aiV4Mapped : AddrInfoFlag

-------------------------------------------------------------------------------
-- AddrInfo
-------------------------------------------------------------------------------

record AddrInfo : Type where
  constructor addrInfo
  field
    addrFlags : List AddrInfoFlag
    addrFamily : AddrFamily
    addrSocketType : SocketType
    addrProtocol : ProtocolNumber
    addrAddress : SocketAddr
    addrCanonName : Maybe (List Char)

open AddrInfo public

defaultHints : AddrInfo
defaultHints = record {
     addrFlags = [];
     addrFamily = afUnspec;
     addrSocketType = sockNone;
     addrProtocol = defaultProtocol;
     addrAddress = SocketAddrIPv4 defaultPort 0;
     addrCanonName = nothing
  }

postulate
  getAddrInfo : Maybe AddrInfo -> Maybe HostName -> Maybe ServiceName
    -> IO (Tuple AddrInfo (List AddrInfo))

-------------------------------------------------------------------------------
-- Socket
-------------------------------------------------------------------------------

postulate
  Socket : Type
  socket : AddrFamily -> SocketType -> ProtocolNumber -> IO Socket
  openSocket : AddrInfo -> IO Socket
  connect : Socket -> SocketAddr -> IO Unit
  bind : Socket -> SocketAddr -> IO Unit
  accept : Socket -> IO (Tuple Socket SocketAddr)
  close : Socket -> IO Unit
  send : Socket -> Bytes -> IO Nat
  sendAll : Socket -> Bytes -> IO Unit
  recv : Socket -> Nat -> IO Bytes
  gracefulClose : Socket -> (milliseconds : Nat) -> IO Unit
  listen : Socket -> Nat -> IO Unit

-------------------------------------------------------------------------------
-- SocketOption
-------------------------------------------------------------------------------

postulate
  SocketOption : Type
  reuseAddr : SocketOption
  setSocketOption : Socket -> SocketOption -> Int -> IO Unit

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC

  import Network.Socket
  import Network.Socket.ByteString
  import Data.Text (Text, pack, unpack)

  getAddrInfo'
    :: Maybe AddrInfo
    -> Maybe Text
    -> Maybe Text
    -> IO (AddrInfo, [AddrInfo])
  getAddrInfo' ai hostname servicename = do
    result <- getAddrInfo ai (unpack <$> hostname) (unpack <$> servicename)
    pure (head result, tail result)
#-}

{-# COMPILE GHC Socket = type Socket #-}
{-# COMPILE GHC socket = socket #-}
{-# COMPILE GHC openSocket = openSocket #-}
{-# COMPILE GHC connect = connect #-}
{-# COMPILE GHC bind = bind #-}
{-# COMPILE GHC listen = \ s n -> listen s (fromInteger n) #-}
{-# COMPILE GHC accept = accept #-}
{-# COMPILE GHC close = close #-}
{-# COMPILE GHC gracefulClose = \ s n -> gracefulClose s (fromInteger n) #-}
{-# COMPILE GHC send = \ s bs -> send s bs >>= pure . toInteger  #-}
{-# COMPILE GHC sendAll = sendAll  #-}
{-# COMPILE GHC recv = \ s n -> recv s (fromInteger n)  #-}

{-# COMPILE GHC SocketOption = type SocketOption #-}
{-# COMPILE GHC reuseAddr = ReuseAddr #-}
{-# COMPILE GHC setSocketOption = \ s o i -> setSocketOption s o (fromInteger i) #-}

{-# COMPILE GHC SocketAddr = type SockAddr #-}
{-# COMPILE GHC socketAddrShow = pack . show #-}

{-# COMPILE GHC AddrInfo = data AddrInfo (AddrInfo) #-}
{-# COMPILE GHC AddrInfoFlag = data AddrInfoFlag (AI_ADDRCONFIG | AI_ALL | AI_CANONNAME | AI_NUMERICHOST | AI_NUMERICSERV | AI_PASSIVE | AI_V4MAPPED) #-}

{-# COMPILE GHC AddrFamily = type Family #-}
{-# COMPILE GHC afInet = AF_INET #-}
{-# COMPILE GHC afUnspec = AF_UNSPEC #-}

{-# COMPILE GHC SocketType = type SocketType #-}
{-# COMPILE GHC sockStream = Stream #-}
{-# COMPILE GHC sockNone = NoSocketType #-}

{-# COMPILE GHC ProtocolNumber = type ProtocolNumber #-}
{-# COMPILE GHC defaultProtocol = defaultProtocol #-}
{-# COMPILE GHC PortNumber = type PortNumber #-}
{-# COMPILE GHC defaultPort = defaultPort #-}
{-# COMPILE GHC SocketAddrIPv4 = SockAddrInet #-}
{-# COMPILE GHC getAddrInfo = getAddrInfo' #-}
