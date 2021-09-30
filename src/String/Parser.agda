{-# OPTIONS --type-in-type #-}

module String.Parser where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (bool)

open import Control.Alternative
open import Data.Char as Char using ()
open import Data.Foldable
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

data Consumed : Set where
  consumed : Bool -> Consumed

data Result (a : Set) : Set where
  ok : a -> String -> Result a
  err : Result a

record Parser (a : Set) : Set where
  constructor toParser
  field unParser : String -> Pair Consumed (Result a)

open Parser

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

private
  pureParser : a -> Parser a
  pureParser x = toParser \ where
    s -> (consumed false , ok x s)

  bindParser : Parser a -> (a -> Parser b) -> Parser b
  bindParser m k = toParser \ where
    s -> case unParser m s of \ where
      (_ , ok x s') -> unParser (k x) s'
      (c , err) -> (c , err)

  mapParser : (a -> b) -> Parser a -> Parser b
  mapParser f x = bindParser x (f >>> pureParser)

  apParser : Parser (a -> b) -> Parser a -> Parser b
  apParser p q = bindParser p \ f -> bindParser q \ x -> pureParser (f x)

instance
  Functor-Parser : Functor Parser
  Functor-Parser .map = mapParser

  Applicative-Parser : Applicative Parser
  Applicative-Parser .pure = pureParser
  Applicative-Parser ._<*>_ = apParser

  Monad-Parser : Monad Parser
  Monad-Parser ._>>=_ = bindParser

  Alternative-Parser : Alternative Parser
  Alternative-Parser .azero = toParser \ where
    s -> (consumed false , err)
  Alternative-Parser ._<|>_ l r = toParser \ where
    s -> case unParser l s of \ where
      (consumed false , err) -> case unParser r s of \ where
        (consumed false , res) -> (consumed false , res)
        other -> other
      other -> other

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

try : Parser a -> Parser a
try p = toParser \ where
  s -> case unParser p s of \ where
    (consumed true , err) -> (consumed false , err)
    other -> other

notFollowedBy : Parser a -> Parser Unit
notFollowedBy p = toParser \ where
  s -> case unParser p s of \ where
    (_ , ok _ _) -> (consumed false , err)
    (_ , err) -> (consumed false , ok tt s)

option : a -> Parser a -> Parser a
option a p = p <|> pure a

{-# TERMINATING #-}
many1 many : Parser a -> Parser (List a)
many1 a = (| a :: many a |)
many a = option [] (many1 a)

optional : Parser a -> Parser (Maybe a)
optional a = (| just a | nothing |)

choose : Parser a -> Parser b -> Parser (Either a b)
choose a b = (| left a | right b |)

exactly : Nat -> Parser a -> Parser (List a)
exactly 0 p = pure []
exactly n p = sequence (List.replicate n p)

between : Parser a -> Parser b -> Parser c -> Parser c
between p p' q = p *> q <* p'

skipMany : Parser a -> Parser Unit
skipMany p = many p *> pure tt

skipMany1 : Parser a -> Parser Unit
skipMany1 p = many1 p *> pure tt

sepBy1 : Parser a -> Parser b -> Parser (List a)
sepBy1 p sep = (| p :: many (sep *> p) |)

sepBy : Parser a -> Parser b -> Parser (List a)
sepBy p sep = option [] (sepBy1 p sep)

endBy : Parser a -> Parser b -> Parser (List a)
endBy p sep = many (p <* sep)

endBy1 : Parser a -> Parser b -> Parser (List a)
endBy1 p sep = many1 (p <* sep)

{-# TERMINATING #-}
prefix : (a -> b) -> Parser (b -> b) -> Parser a -> Parser b
prefix wrap op p = op <*> prefix wrap op p <|> wrap <$> p

{-# TERMINATING #-}
postfix : (a -> b) -> Parser a -> Parser (b -> b) -> Parser b
postfix wrap p op = (| (wrap <$> p) # s' |)
  where s' = option id (| op >>> s' |)

{-# TERMINATING #-}
infixl1 : (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
infixl1 wrap p op = postfix wrap p (| flip op p |)

{-# TERMINATING #-}
infixr1 : (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
infixr1 wrap p op = (| p # (| flip op (infixr1 wrap p op) |) <|> pure wrap |)

chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = infixl1 id

chainl : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = option a (chainl1 p op)

chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 = infixr1 id

chainr : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op a = option a (chainr1 p op)

-------------------------------------------------------------------------------
-- Char parsers
-------------------------------------------------------------------------------

anyChar : Parser Char
anyChar = toParser \ where
  s -> if s == ""
    then (consumed false , err)
    else (consumed true , uncurry ok (String.uncons s {{trustMe}}))

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
oneOf cs = satisfy (_elem cs)

noneOf : List Char -> Parser Char
noneOf cs = satisfy (_notElem cs)

alpha : Parser Char
alpha = satisfy Char.isAlpha

lower : Parser Char
lower = satisfy Char.isLower

upper : Parser Char
upper = satisfy (| Char.isAlpha && (not <<< Char.isLower) |)

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
word = option "" word1
word1 = (| String.cons alpha word |)

takeWhile : (Char -> Bool) -> Parser String
takeWhile p = toParser \ where
  s -> (consumed true , uncurry ok (String.break p s))

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
fully = between skipSpaces eof

lexeme : Parser a -> Parser a
lexeme p = p <* skipSpaces

symbol : String -> Parser String
symbol = lexeme <<< string

token : Parser a -> Parser a
token = lexeme <<< try

keyword : String -> Parser Unit
keyword s = token (string s *> notFollowedBy alphaNum)

-------------------------------------------------------------------------------
-- Running parsers
-------------------------------------------------------------------------------

runParser : Parser a -> String -> Maybe a
runParser p s = case unParser p s of \ where
 (_ , ok x _) -> just x
 _ -> nothing
