open import Prelude

open import Control.Selective
open import Control.Monad.Maybe.Trans
open import Data.Monoid.Foldable
open import System.IO

-- prog1 prog2 prog3 prog : IO (Either Unit String)
-- prog1 = pure (right "prog1")
-- prog2 = undefined
-- prog3 = pure (right "prog3")
-- prog = prog1 orElse prog2 orElse prog3

-- main : IO Unit
-- main = do
--   res <- prog
--   case res \ where
--     (left tt) -> putStrLn "oops"
--     (right s) -> putStrLn s

-- prog1 prog2 : IO (Maybe String)
-- prog3 prog : IO String
-- prog1 = putStrLn "1" >> (pure nothing)
-- prog2 = putStrLn "2" >> (pure (just "prog2"))
-- prog3 = putStrLn "3" >> (pure "prog3")
-- prog = fromMaybeS prog1 (fromMaybeS prog2 prog3)

-- main : IO Unit
-- main = prog >>= putStrLn

prog1 prog2 : MaybeT IO String
prog3 prog : IO String
prog1 = lift (putStrLn "1") >> hoistMaybe nothing
prog2 = lift (putStrLn "2") >> pure "prog2"
prog3 = undefined
prog = fromMaybeS (runMaybeT (prog1 <|> prog2)) prog3
prog' = fromMaybeT (prog1 <|> prog2) prog3

main : IO Unit
main = prog' >>= print