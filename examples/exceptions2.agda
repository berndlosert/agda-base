open import Prelude

open import Control.Exception
open import System.IO

data Dummy : Set where
  aDummy : Dummy

instance
  Show-Dummy : Show Dummy
  Show-Dummy .showsPrec _ aDummy = showString "aDummy"

postulate
  instance
    Exception-Dummy : Exception Dummy

{-# FOREIGN GHC
  import Control.Exception
  import MAlonzo.Code.Control.Exception (ExceptionDict (..))

  data Dummy = Dummy
    deriving (Show)

  instance Exception Dummy
#-}

{-# COMPILE GHC Dummy = data Dummy (Dummy) #-}
{-# COMPILE GHC Exception-Dummy = ExceptionDict #-}

printer : IO (Either Dummy Unit) -> IO Unit
printer x = x >>= print

main : IO Unit
main = do
  --printer $ try $ throwIO Dummy
  printer $ try $ throw aDummy
  --printer $ try $ evaluate $ throw Dummy
  printer $ try $ join $ pure $! throw aDummy
  printer $ try $ join $ pure $ throw aDummy
 