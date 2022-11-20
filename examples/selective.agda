open import Prelude

open import Control.Selective
open import Control.Monad.Maybe.Trans
open import Data.Foldable
open import System.IO

-- prog1 prog2 prog3 prog : IO (Either Unit String)
-- prog1 = pure $ right "prog1"
-- prog2 = undefined
-- prog3 = pure $ right "prog3"
-- prog = prog1 orElse prog2 orElse prog3

-- main : IO Unit
-- main = do
--   res <- prog
--   case res of \ where
--     (left tt) -> putStrLn "oops"
--     (right s) -> putStrLn s

-- prog1 prog2 : IO (Maybe String)
-- prog3 prog : IO String
-- prog1 = pure $ just "prog1"
-- prog2 = undefined
-- prog3 = pure $ "prog3"
-- prog = prog1 <?:> prog2 <?:> prog3
-- prog' = (| prog1 ?: (| prog2 ?: prog3 |) |)

-- main : IO Unit
-- main = prog' >>= putStrLn

prog1 prog2 prog3 prog : MaybeT IO String
prog1 = hoistMaybeT nothing
prog2 = pure "prog2"
prog3 = undefined
prog = prog1 <|> prog2 <|> prog3

main : IO Unit
main = runMaybeT prog >>= print