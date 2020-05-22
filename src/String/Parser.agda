{-# OPTIONS --type-in-type #-}

module String.Parser where

open import Prelude
  hiding (count)

open import Control.Monad.State.Trans
import Data.List as List
import Data.String as String

private variable A B C : Set

--------------------------------------------------------------------------------
-- Parser (definition and instances)
--------------------------------------------------------------------------------

abstract
  Parser = StateT String List

  parser : (String -> List (A * String)) -> Parser A
  parser = stateT:

  runParser : Parser A -> String -> List (A * String)
  runParser = runStateT

  instance
    functorParser : Functor Parser
    functorParser = functorStateT

    applicativeParser : Applicative Parser
    applicativeParser = applicativeStateT

    alternativeParser : Alternative Parser
    alternativeParser = alternativeStateT

    monadParser : Monad Parser
    monadParser = monadStateT

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

{-# NON_TERMINATING #-}
many1 many : Parser A -> Parser (List A)
many1 a = (| _::_ a (many a) |)
many a = many1 a <|> pure []

optional : Parser A -> Parser (Maybe A)
optional a = (| just a | nothing |)

eitherP : Parser A -> Parser B -> Parser (A + B)
eitherP a b = (| left a | right b |)

choice : List (Parser A) -> Parser A
choice ps = foldr _<|>_ empty ps

count : Nat -> Parser A -> Parser (List A)
count 0 p = pure []
count n p = sequence (replicate n p)

between : Parser A -> Parser B -> Parser C -> Parser C
between p p' q = p *> (q <* p')

option : A -> Parser A -> Parser A
option a p = p <|> pure a

skipMany : Parser A -> Parser Unit
skipMany p = many p *> pure unit

skipMany1 : Parser A -> Parser Unit
skipMany1 p = many1 p *> pure unit

sepBy1 : Parser A -> Parser B -> Parser (List A)
sepBy1 p sep = (| _::_ p (many $ sep *> p) |)

sepBy : Parser A -> Parser B -> Parser (List A)
sepBy p sep = sepBy1 p sep <|> pure []

endBy : Parser A -> Parser B -> Parser (List A)
endBy p sep = many (p <* sep)

endBy1 : Parser A -> Parser B -> Parser (List A)
endBy1 p sep = many1 (p <* sep)

{-# TERMINATING #-}
chainl1 : Parser A -> Parser (A -> A -> A) -> Parser A
chainl1 p op = p >>= rest
  where
    rest : _
    rest x = (do
      f <- op
      y <- p
      rest (f x y)) <|> return x

chainl : Parser A -> Parser (A -> A -> A) -> A -> Parser A
chainl p op a = chainl1 p op <|> pure a

{-# TERMINATING #-}
chainr1 : Parser A -> Parser (A -> A -> A) -> Parser A
chainr1 p op = scan
  where
    scan rest : _
    scan = p >>= rest
    rest x = (do
      f <- op
      y <- scan
      rest (f x y)) <|> return x

chainr : Parser A -> Parser (A -> A -> A) -> A -> Parser A
chainr p op a = chainr1 p op <|> pure a

-- Run a parser on a string and get the first result.
parse : Parser A -> String -> Maybe A
parse p s with runParser p s
... | [] = nothing
... | ((a , _) :: _) = just a

--------------------------------------------------------------------------------
-- Char parsers
--------------------------------------------------------------------------------

anyChar : Parser Char
anyChar = parser (maybeToList <<< String.uncons)

satisfy : (Char -> Bool) -> Parser Char
satisfy p = do
  c <- anyChar
  if p c then pure c else empty

skipWhile : (Char -> Bool) -> Parser Unit
skipWhile p = do
  c <- anyChar
  if p c then pure unit else empty

skipAll : Parser Unit
skipAll = skipWhile (const true)

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

--------------------------------------------------------------------------------
-- String parsers
--------------------------------------------------------------------------------

{-# TERMINATING #-}
string : String -> Parser String
string s with String.uncons s
... | nothing = pure ""
... | (just (c , s')) = char c *> string s' *> pure (cons c s')

{-# TERMINATING #-}
word : Parser String
word = neword <|> (pure "")
  where
    neword : Parser String
    neword = do
      c <- letter
      s <- word
      return (cons c s)

takeWhile : (Char -> Bool) -> Parser String
takeWhile p = parser \ s ->
  singleton (String.takeWhile p s , String.dropWhile p s)

takeAll : Parser String
takeAll = takeWhile (const true)

--------------------------------------------------------------------------------
-- Parsers for numbers
--------------------------------------------------------------------------------

nat : Parser Nat
nat = chainl1
    (digit >>= \ n -> return $ monus (ord n) (ord '0'))
    (return \ m n -> 10 * m + n)

int : Parser Int
int = (| neg (char '-' *> nat) | pos (char '+' *> nat) | pos nat |)
