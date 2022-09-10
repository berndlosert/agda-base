open import Prelude

open import Control.Monad.State.Trans
open import Control.Monad.Either.Trans
open import System.IO
open import Control.Monad.IO.Class

ParserT : Set -> (Set -> Set) -> Set -> Set
ParserT s m a = StateT s m a

record Person : Set where
  constructor asPerson
  field
    firstName : String
    lastName : String
    age : Int

open Person

validateName : ParserT String IO (Maybe String)
validateName = do
  name <- get
  liftIO $ print $ "validating name: " <> name
  pure nothing

validateAge : ParserT Nat IO (Maybe String)
validateAge = do
  age <- get
  if (age > 100)
    then pure $ just "age is too high"
    else pure nothing

validatePerson : ParserT Person IO (Maybe String)
validatePerson = do
  person <- get
  liftIO $ print "checking first name"
  runStateT validateName (person .firstName)
