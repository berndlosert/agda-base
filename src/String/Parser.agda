{-# OPTIONS --type-in-type #-}

module String.Parser where

open import Prelude hiding (bool)

open import Control.Alternative
open import Control.Monad.State.Trans
open import Data.Char as Char using ()
open import Data.List as List using ()
open import Data.String as String using ()
open import Data.Traversable

private variable a b c : Set

-------------------------------------------------------------------------------
-- Parser (definition and instances)
-------------------------------------------------------------------------------

abstract
  Parser : Set -> Set
  Parser = StateT String List

  parser : (String -> List (Pair String a)) -> Parser a
  parser = StateT:

  runParser : Parser a -> String -> List (Pair String a)
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

{-# NON_TERMINATING #-}
many1 many : Parser a -> Parser (List a)
many1 a = (| _::_ a (many a) |)
many a = many1 a <|> pure []

optional : Parser a -> Parser (Maybe a)
optional a = (| Just a | Nothing |)

choose : Parser a -> Parser b -> Parser (Either a b)
choose a b = (| Left a | Right b |)

choice : List (Parser a) -> Parser a
choice ps = List.foldr _<|>_ empty ps

exactly : Nat -> Parser a -> Parser (List a)
exactly 0 p = pure []
exactly n p = List.sequence (List.replicate n p)

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

{-# NON_TERMINATING #-}
chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 {a} p op = (| _#_ p rest |)
  where
    rest : Parser (a -> a)
    rest = (| _>>>_ (| flip op p |) rest | id |)

chainl : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = chainl1 p op <|> pure a

{-# NON_TERMINATING #-}
chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 {a} p op = (| _#_ p rest |)
  where
    rest : Parser (a -> a)
    rest = (| flip op (chainr1 p op) | id |)

chainr : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op a = chainr1 p op <|> pure a

-- Run a parser on a string and get the first result.
parse : Parser a -> String -> Maybe a
parse p s =
  case runParser p s of \ where
    [] -> Nothing
    ((_ , a) :: _) -> Just a

-------------------------------------------------------------------------------
-- Char parsers
-------------------------------------------------------------------------------

anyChar : Parser Char
anyChar = parser (String.uncons >>> maybe [] (swap >>> List.singleton))

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
oneOf cs = satisfy (\ c -> List.elem c cs)

noneOf : List Char -> Parser Char
noneOf cs = satisfy (\ c -> List.notElem c cs)

letter : Parser Char
letter = satisfy Char.isAlpha

lower : Parser Char
lower = satisfy Char.isLower

upper : Parser Char
upper = satisfy (\ c -> Char.isAlpha c && not (Char.isLower c))

digit : Parser Char
digit = satisfy Char.isDigit

hexDigit : Parser Char
hexDigit = satisfy Char.isHexDigit

alphaNum : Parser Char
alphaNum = letter <|> digit

space : Parser Char
space = satisfy Char.isSpace

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
string = map String.pack <<< traverse char <<< String.unpack

{-# NON_TERMINATING #-}
word : Parser String
word1 : Parser String
word = word1 <|> (pure "")
word1 = do
  c <- letter
  s <- word
  pure (String.cons c s)

takeWhile : (Char -> Bool) -> Parser String
takeWhile p = parser \ s -> List.singleton (String.break p s)

takeAll : Parser String
takeAll = takeWhile (const True)

-------------------------------------------------------------------------------
-- Parsers for numbers
-------------------------------------------------------------------------------

nat : Parser Nat
nat = chainl1 digit' (pure \ m n -> 10 * m + n)
  where
    digit' : Parser Nat
    digit' = do
      n <- digit
      pure $ fromMaybe
        (error "String.Parser.nat")
        (Char.toDigit n)

int : Parser Int
int = (| neg (char '-' *> nat) | Pos (char '+' *> nat) | Pos nat |)

-------------------------------------------------------------------------------
-- Misc. parsers
-------------------------------------------------------------------------------

lexeme : Parser a -> Parser a
lexeme p = p <* skipSpaces

symbol : String -> Parser String
symbol s = lexeme (string s)
