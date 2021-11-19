open import Prelude

open import Control.Exception
open import System.IO

data MyException : Set where
  ThisException ThatException : MyException

postulate
  instance
    Exception-MyException : Exception MyException

{-# FOREIGN GHC
  import Control.Exception
  import MAlonzo.Code.Control.Exception (ExceptionDict (..))

  data MyException = ThisException | ThatException
    deriving Show

  instance Exception MyException
#-}

{-# COMPILE GHC MyException = data MyException (ThisException | ThatException) #-}
{-# COMPILE GHC Exception-MyException = ExceptionDict #-}

main : IO Unit
main =
  (throw ThisException)
    catch (\ (e : MyException) -> throw ThatException)
    catch (\ (e : MyException) -> putStrLn "oops")
