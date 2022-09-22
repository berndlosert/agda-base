open import Prelude

open import Control.Exception
open import System.IO

data MyException : Set where
  ThisException ThatException : MyException

postulate
  instance
    Exception-MyException : Exception MyException

  unsafeFun : Bool -> IO Bool

{-# FOREIGN GHC
  import Control.Exception
  import MAlonzo.Code.Control.Exception (ExceptionDict (..))

  data MyException = ThisException | ThatException
    deriving Show

  instance Exception MyException

  unsafeFun :: Bool -> IO Bool
  unsafeFun _ = ioError (userError "oh no")
#-}

{-# COMPILE GHC MyException = data MyException (ThisException | ThatException) #-}
{-# COMPILE GHC Exception-MyException = ExceptionDict #-}
{-# COMPILE GHC unsafeFun = unsafeFun #-}

main : IO Unit
main = do
  (throw ThisException)
    catch (\ (e : MyException) -> throw ThatException)
    catch (\ (e : MyException) -> putStrLn "oops")
  (throw (userException "oops"))
    catch (\ (e : IOException) -> putStrLn "caught ya")
  b <- (unsafeFun true) catch (\ (e : IOException) -> pure true)
  print b
  putStrLn "the end"
