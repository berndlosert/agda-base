{-# OPTIONS --type-in-type #-}

module String.Parser where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (bool)

open import Control.Alternative
open import Data.Char as Char using ()
open import Data.List as List using ()
open import Data.String as String using ()
open import Data.Traversable

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Alternative public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set

-------------------------------------------------------------------------------
-- Parser
-------------------------------------------------------------------------------

pattern consumed = true
pattern unconsumed = false

data Result (a : Set) : Set where
  ok : Bool -> Pair a String -> Result a
  err : Bool -> Result a

record Parser (a : Set) : Set where
  constructor toParser
  field runParser : String -> Result a

open Parser

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-Parser : Functor Parser
  Functor-Parser .map f p = toParser \ where
    input -> case runParser p input of \ where
      (ok b (x , rest)) -> ok b (f x , rest)
      (err b) -> err b

  Applicative-Parser : Applicative Parser
  Applicative-Parser .pure x = toParser \ where
    input -> ok unconsumed (x , input)
  Applicative-Parser ._<*>_ p q = toParser \ where
    input -> case runParser p input of \ where
      (ok unconsumed (f , rest)) -> runParser (map f q) rest
      (ok consumed (f , rest)) -> case runParser (map f q) rest of \ where
        (ok _ out) -> ok consumed out
        (err _) -> err consumed
      (err b) -> err b

  Alternative-Parser : Alternative Parser
  Alternative-Parser .azero = toParser \ where
    input -> err unconsumed
  Alternative-Parser ._<|>_ l r = toParser \ where
    input -> case runParser l input of \ where
      (err unconsumed) -> runParser r input
      (ok unconsumed out) -> case runParser r input of \ where
        (ok consumed out') -> ok consumed out'
        (ok unconsumed out') -> ok unconsumed out
        (err b) -> err b
      (err consumed) -> err consumed
      (ok consumed out) -> ok consumed out

  Monad-Parser : Monad Parser
  Monad-Parser ._>>=_ m k = toParser \ where
    input -> case runParser m input of \ where
      (ok unconsumed (x , rest)) -> runParser (k x) rest
      (ok consumed (x , rest)) -> case runParser (k x) rest of \ where
        (ok _ out) -> ok consumed out
        (err _) -> err consumed
      (err b) -> err b

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

try : Parser a -> Parser a
try p = toParser \ where
  input -> case runParser p input of \ where
    (err consumed) -> err unconsumed
    res -> res

{-# TERMINATING #-}
many1 many : Parser a -> Parser (List a)
many1 a = (| a :: many a |)
many a = many1 a <|> pure []

optional : Parser a -> Parser (Maybe a)
optional a = (| just a | nothing |)

choose : Parser a -> Parser b -> Parser (Either a b)
choose a b = (| left a | right b |)

exactly : Nat -> Parser a -> Parser (List a)
exactly 0 p = pure []
exactly n p = List.sequence (List.replicate n p)

between : Parser a -> Parser b -> Parser c -> Parser c
between p p' q = p *> q <* p'

option : a -> Parser a -> Parser a
option a p = p <|> pure a

skipMany : Parser a -> Parser Unit
skipMany p = many p *> pure tt

skipMany1 : Parser a -> Parser Unit
skipMany1 p = many1 p *> pure tt

sepBy1 : Parser a -> Parser b -> Parser (List a)
sepBy1 p sep = (| p :: many (sep *> p) |)

sepBy : Parser a -> Parser b -> Parser (List a)
sepBy p sep = sepBy1 p sep <|> pure []

endBy : Parser a -> Parser b -> Parser (List a)
endBy p sep = many (p <* sep)

endBy1 : Parser a -> Parser b -> Parser (List a)
endBy1 p sep = many1 (p <* sep)

{-# TERMINATING #-}
prefix : (a -> b) -> Parser (b -> b) -> Parser a -> Parser b
prefix wrap op p = op <*> prefix wrap op p <|> wrap <$> p

{-# TERMINATING #-}
postfix : (a -> b) -> Parser a -> Parser (b -> b) -> Parser b
postfix wrap p op = (| (wrap <$> p) # rest |)
  where rest = (| op >>> rest |) <|> pure id

{-# TERMINATING #-}
infixl1 : (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
infixl1 wrap p op = postfix wrap p (| flip op p |)

{-# TERMINATING #-}
infixr1 : (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
infixr1 wrap p op = (| p # (| flip op (infixr1 wrap p op) |) <|> pure wrap |)

chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = infixl1 id

chainl : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = chainl1 p op <|> pure a

chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 = infixr1 id

chainr : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op a = chainr1 p op <|> pure a

notFollowedBy : Parser a -> Parser Unit
notFollowedBy p = try ((p *> azero) <|> pure tt)

-------------------------------------------------------------------------------
-- Char parsers
-------------------------------------------------------------------------------

anyChar : Parser Char
anyChar = toParser \ where
  s -> if s == ""
    then err unconsumed
    else ok consumed (String.uncons s {{trustMe}})

eof : Parser Unit
eof = notFollowedBy anyChar

satisfy : (Char -> Bool) -> Parser Char
satisfy test = do
  c <- anyChar
  if test c then pure c else azero

skipWhile : (Char -> Bool) -> Parser Unit
skipWhile p = do
  c <- anyChar
  if p c then pure tt else azero

skipAll : Parser Unit
skipAll = skipWhile (const true)

char : Char -> Parser Char
char c = satisfy (c ==_)

oneOf : List Char -> Parser Char
oneOf cs = satisfy (\ c -> List.elem c cs)

noneOf : List Char -> Parser Char
noneOf cs = satisfy (\ c -> List.notElem c cs)

alpha : Parser Char
alpha = satisfy Char.isAlpha

lower : Parser Char
lower = satisfy Char.isLower

upper : Parser Char
upper = satisfy (\ c -> Char.isAlpha c && not (Char.isLower c))

digit : Parser Char
digit = satisfy Char.isDigit

hexDigit : Parser Char
hexDigit = satisfy Char.isHexDigit

alphaNum : Parser Char
alphaNum = alpha <|> digit

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

{-# TERMINATING #-}
word : Parser String
word1 : Parser String
word = word1 <|> (pure "")
word1 = (| String.cons alpha word |)

takeWhile : (Char -> Bool) -> Parser String
takeWhile p = toParser (ok consumed <<< String.break p)

takeAll : Parser String
takeAll = takeWhile (const true)

-------------------------------------------------------------------------------
-- Parsers for numbers
-------------------------------------------------------------------------------

nat : Parser Nat
nat = chainl1 digit' (pure \ m n -> 10 * m + n)
  where
    digit' : Parser Nat
    digit' = do
      n <- digit
      pure (Char.toDigit n {{trustMe}})

int : Parser Int
int = (| neg (char '-' *> nat) | pos (char '+' *> nat) | pos nat |)

-------------------------------------------------------------------------------
-- Misc. parsers
-------------------------------------------------------------------------------

fully : Parser a -> Parser a
fully p = skipSpaces *> p <* eof

lexeme : Parser a -> Parser a
lexeme p = p <* skipSpaces

symbol : String -> Parser String
symbol s = lexeme (string s)

-------------------------------------------------------------------------------
-- Executing parsers
-------------------------------------------------------------------------------

execParser : Parser a -> String -> Maybe a
execParser p input = case runParser p input of \ where
 (ok _ (x , _)) -> just x
 _ -> nothing
