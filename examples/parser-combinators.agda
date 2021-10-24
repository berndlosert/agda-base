open import Prelude
  hiding (Sub)

open import Data.String
open import String.Parser
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
  Show-Expr .showsPrec prec = \ where
    (Num n) -> showParen (prec > appPrec) $ showString "Num " <<< showsPrec appPrec+1 n
    (Neg e) -> showParen (prec > appPrec) $ showString "Neg " <<< showsPrec appPrec+1 e
    (Var s) -> showParen (prec > appPrec) $ showString "Var " <<< showString s
    (Add l r) -> showParen (prec > appPrec) $ showString "Add " <<< showsPrec appPrec+1 l <<< showString " " <<< showsPrec appPrec+1 r
    (Mul l r) -> showParen (prec > appPrec) $ showString "Mul " <<< showsPrec appPrec+1 l <<< showString " " <<< showsPrec appPrec+1 r
    (Sub l r) -> showParen (prec > appPrec) $ showString "Sub " <<< showsPrec appPrec+1 l <<< showString " " <<< showsPrec appPrec+1 r

ident = pack <$> (| alpha :: many alphaNum |)

{-# TERMINATING #-}
expr term negate atom : Parser Expr
expr = chainl1 term (Add <$ token (char '+') <|> Sub <$ token (char '-'))
term = chainl1 negate (Mul <$ token (char '*'))
negate = Neg <$> (keyword "negate" *> negate) <|> atom
atom = token (char '(') *> expr <* token (char ')') <|> (| Num (lexeme nat) | Var (lexeme ident) |)

test = lexeme (char '(') *> lexeme nat <* lexeme (char ')')

main : IO Unit
main = do
  print $ runParser expr "( x + 7 ) "
  print $ runParser expr "x + 7"
  print $ runParser (expr <* eof) "x + 7"
  print $ runParser expr "negatex"
