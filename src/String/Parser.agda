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
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set

-------------------------------------------------------------------------------
-- Parser
-------------------------------------------------------------------------------

data Reply (a : Set) : Set where
  ok : a -> String -> Reply a
  err : Reply a

data Consumed (a : Set) : Set where
  consumed : Reply a -> Consumed a
  empty : Reply a -> Consumed a

record Parser (a : Set) : Set where
  constructor toParser
  field runParser : String -> Consumed a

open Parser

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-Parser : Functor Parser
  Functor-Parser .map f p = toParser \ where
    s -> case runParser p s of \ where
      (empty (ok x s')) -> empty (ok (f x) s')
      (consumed (ok x s')) -> consumed (ok (f x) s')
      (empty err) -> empty err
      (consumed err) -> consumed err

  Applicative-Parser : Applicative Parser
  Applicative-Parser .pure x = toParser (empty <<< ok x)
  Applicative-Parser ._<*>_ p q = toParser \ where
    s -> case runParser p s of \ where
      (empty (ok f s')) -> runParser (map f q) s'
      (consumed (ok f s')) -> runParser (map f q) s'
      (empty err) -> empty err
      (consumed err) -> consumed err

  Alternative-Parser : Alternative Parser
  Alternative-Parser .azero = toParser \ where
    s -> empty err
  Alternative-Parser ._<|>_ l r = toParser \ where
    s -> case runParser l s of \ where
      (empty err) -> runParser r s
      (empty anok) -> case runParser r s of \ where
        (empty _) -> empty anok
        aconsumed -> aconsumed
      aconsumed -> aconsumed

  Monad-Parser : Monad Parser
  Monad-Parser ._>>=_ m k = toParser \ where
    s -> case runParser m s of \ where
      (empty (ok x s')) -> runParser (k x) s'
      (empty err) -> empty err
      (consumed (ok x s')) -> case runParser (k x) s' of \ where
        (consumed areply) -> consumed areply
        (empty areply) -> consumed areply
      (consumed err) -> consumed err

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

try : Parser a -> Parser a
try p = toParser \ where
  s -> case runParser p s of \ where
    (consumed err) -> empty err
    (consumed anok) -> consumed anok
    anempty -> anempty

notFollowedBy : Parser a -> Parser Unit
notFollowedBy p = try ((p *> azero) <|> pure tt)

{-# NON_TERMINATING #-}
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
between p p' q = p *> (q <* p')

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

{-# NON_TERMINATING #-}
prefix : (a -> b) -> Parser (b -> b) -> Parser a -> Parser b
prefix wrap op p = op <*> prefix wrap op p <|> wrap <$> p

{-# NON_TERMINATING #-}
postfix : (a -> b) -> Parser a -> Parser (b -> b) -> Parser b
postfix wrap p op = (| (wrap <$> p) # rest |)
  where rest = (| op >>> rest |) <|> pure id

{-# NON_TERMINATING #-}
infixl1 : (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
infixl1 wrap p op = postfix wrap p (| flip op p |)

{-# NON_TERMINATING #-}
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

parse : Parser a -> String -> Maybe a
parse p s = case runParser p s of \ where
 (consumed (ok x _)) -> just x
 (empty (ok x _)) -> just x
 _ -> nothing

-------------------------------------------------------------------------------
-- Char parsers
-------------------------------------------------------------------------------

anyChar : Parser Char
anyChar = toParser \ where
  s -> if s == ""
    then empty err
    else consumed (uncurry ok (String.uncons s {{trustMe}}))

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
takeWhile p = toParser \ s -> consumed (uncurry ok (String.break p s))

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

eof : Parser Unit
eof = notFollowedBy anyChar

fully : Parser a -> Parser a
fully p = skipSpaces *> p <* eof

lexeme : Parser a -> Parser a
lexeme p = p <* skipSpaces

symbol : String -> Parser String
symbol s = lexeme (string s)
