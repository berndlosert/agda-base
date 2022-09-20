open import Prelude

open import Data.String
open import Data.String.Builder
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
    (Num n) -> showParen (prec > appPrec) $ "Num " <> showsPrec appPrec+1 n
    (Neg e) -> showParen (prec > appPrec) $ "Neg " <> showsPrec appPrec+1 e
    (Var s) -> showParen (prec > appPrec) $ "Var " <> toBuilder s
    (Add l r) -> showParen (prec > appPrec) $ "Add " <> showsPrec appPrec+1 l <> " " <> showsPrec appPrec+1 r
    (Mul l r) -> showParen (prec > appPrec) $ "Mul " <> showsPrec appPrec+1 l <> " " <> showsPrec appPrec+1 r
    (Sub l r) -> showParen (prec > appPrec) $ "Sub " <> showsPrec appPrec+1 l <> " " <> showsPrec appPrec+1 r

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
