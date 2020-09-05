module String.Parser where

open import Prelude
  hiding (count)

open import Control.Monad.State.Trans
open import Data.String as String using ()

private variable a b c : Set

-------------------------------------------------------------------------------
-- Parser (definition and instances)
-------------------------------------------------------------------------------

abstract
  Parser = StateT String List

  Parser: : (String -> List (a * String)) -> Parser a
  Parser: = StateT:

  runParser : Parser a -> String -> List (a * String)
  runParser = runStateT

  instance
    Functor-Parser : Functor Parser
    Functor-Parser = Functor-StateT

    Applicative-Parser : Applicative Parser
    Applicative-Parser = Applicative-StateT

    Alternative-Parser : Alternative Parser
    Alternative-Parser = Alternative-StateT

    Monad-Parser : Monad Parser
    Monad-Parser = Monad-StateT

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

many1 many : Parser a -> Parser (List a)
many1 a = (| _::_ a (many a) |)
many a = many1 a <|> pure []

optional : Parser a -> Parser (Maybe a)
optional a = (| Just a | Nothing |)

eitherP : Parser a -> Parser b -> Parser (a + b)
eitherP a b = (| Left a | Right b |)

choice : List (Parser a) -> Parser a
choice ps = foldr _<|>_ empty ps

exactly : Nat -> Parser a -> Parser (List a)
exactly 0 p = pure []
exactly n p = sequence (replicate n p)

between : Parser a -> Parser b -> Parser c -> Parser c
between p p' q = p *> (q <* p')

option : a -> Parser a -> Parser a
option a p = p <|> pure a

skipMany : Parser a -> Parser Unit
skipMany p = many p *> pure unit

skipMany1 : Parser a -> Parser Unit
skipMany1 p = many1 p *> pure unit

sepBy1 : Parser a -> Parser b -> Parser (List a)
sepBy1 p sep = (| _::_ p (many (sep *> p)) |)

sepBy : Parser a -> Parser b -> Parser (List a)
sepBy p sep = sepBy1 p sep <|> pure []

endBy : Parser a -> Parser b -> Parser (List a)
endBy p sep = many (p <* sep)

endBy1 : Parser a -> Parser b -> Parser (List a)
endBy1 p sep = many1 (p <* sep)

chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = p >>= rest
  where
    rest : _
    rest x = (do
      f <- op
      y <- p
      rest (f x y)) <|> return x

chainl : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = chainl1 p op <|> pure a

chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = scan
  where
    scan rest : _
    scan = p >>= rest
    rest x = (do
      f <- op
      y <- scan
      rest (f x y)) <|> return x

chainr : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op a = chainr1 p op <|> pure a

-- Run a parser on a string and get the first result.
parse : Parser a -> String -> Maybe a
parse p s with runParser p s
... | [] = Nothing
... | ((a , _) :: _) = Just a

-------------------------------------------------------------------------------
-- Char parsers
-------------------------------------------------------------------------------

anyChar : Parser Char
anyChar = Parser: (maybeToList <<< String.uncons)

satisfy : (Char -> Bool) -> Parser Char
satisfy p = do
  c <- anyChar
  if p c then pure c else empty

skipWhile : (Char -> Bool) -> Parser Unit
skipWhile p = do
  c <- anyChar
  if p c then pure unit else empty

skipAll : Parser Unit
skipAll = skipWhile (const True)

char : Char -> Parser Char
char c = satisfy (c ==_)

oneOf : List Char -> Parser Char
oneOf cs = satisfy (\ c -> elem c cs)

noneOf : List Char -> Parser Char
noneOf cs = satisfy (\ c -> notElem c cs)

letter : Parser Char
letter = satisfy isAlpha

lower : Parser Char
lower = satisfy isLower

upper : Parser Char
upper = satisfy (isAlpha && not isLower)

digit : Parser Char
digit = satisfy isDigit

hexDigit : Parser Char
hexDigit = satisfy isHexDigit

alphaNum : Parser Char
alphaNum = letter <|> digit

space : Parser Char
space = satisfy isSpace

skipSpaces : Parser Unit
skipSpaces = skipMany space

newline : Parser Char
newline = char '\n'

crlf : Parser Char
crlf = char '\r' *> newline

endOfLine : Parser Char
endOfLine = newline <|> crlf

tab : Parser Char
tab = char '\t'

-------------------------------------------------------------------------------
-- String parsers
-------------------------------------------------------------------------------

string : String -> Parser String
string s with String.uncons s
... | Nothing = pure ""
... | (Just (c , s')) = char c *> string s' *> pure (cons c s')

word : Parser String
word1 : Parser String
word = word1 <|> (pure "")
word1 = do
  c <- letter
  s <- word
  return (cons c s)

takeWhile : (Char -> Bool) -> Parser String
takeWhile p = Parser: \ s ->
  singleton (String.takeWhile p s , String.dropWhile p s)

takeAll : Parser String
takeAll = takeWhile (const True)

-------------------------------------------------------------------------------
-- Parsers for numbers
-------------------------------------------------------------------------------

nat : Parser Nat
nat = chainl1
    (digit >>= \ n -> return (ord n - ord '0'))
    (return \ m n -> 10 * m + n)

int : Parser Int
int = (| neg (char '-' *> nat) | Pos (char '+' *> nat) | Pos nat |)

-------------------------------------------------------------------------------
-- Misc. parsers
-------------------------------------------------------------------------------

lexeme : Parser a -> Parser a
lexeme p = p <* skipSpaces

symbol : String -> Parser String
symbol = lexeme <<< string
