open import Prelude hiding (Num)

open import Data.String
open import Data.String.Parser
open import Data.String.Show
open import System.IO

data Expr : Set where
  Num : Nat -> Expr
  Neg : Expr -> Expr
  Add : Expr -> Expr -> Expr
  Var : String -> Expr
  Mul : Expr -> Expr -> Expr
  Sub : Expr -> Expr -> Expr

instance
  Show-Expr : Show Expr
  Show-Expr .show = showDefault
  Show-Expr .showsPrec prec = \ where
    (Num n) -> showsUnaryWith showsPrec "Num" prec n
    (Neg e) -> showsUnaryWith showsPrec "Neg" prec e
    (Var s) -> showsUnaryWith showsPrec "Neg" prec s
    (Add l r) -> showsBinaryWith showsPrec showsPrec "Add" prec l r
    (Mul l r) -> showsBinaryWith showsPrec showsPrec "Mul" prec l r
    (Sub l r) -> showsBinaryWith showsPrec showsPrec "Sub" prec l r

ident = pack <$> (| alpha :: many alphaNum |)

expr term negate atom : Parser Expr
expr = chainl1 term (Add <$ token (char '+') <|> Sub <$ token (char '-'))
term = chainl1 negate (Mul <$ token (char '*'))
negate = Neg <$> (keyword "negate" *> negate) <|> atom
atom = token (char '(') *> expr <* token (char ')') <|> (| Num (lexeme nat) | Var (lexeme ident) |)

test = lexeme (char '(') *> lexeme nat <* lexeme (char ')')

main : IO Unit
main = do
  --print $ runParser (many $ string "") "abc"
  print $ runParser expr "( x + 7 ) "
  print $ runParser expr "x + 7"
  print $ runParser (expr <* eof) "x + 7"
  print $ runParser expr "negatex"
