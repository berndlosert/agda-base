{-# OPTIONS --type-in-type #-}

module String.Parser where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (bool)

open import Data.Char as Char using ()
open import Data.Foldable
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

record Parser (a : Set) : Set where
  constructor toParser
  field
    unParser : forall {b}
      -> String
      -> (cok : a -> String -> b) (cerr : b)
      -> (eok : a -> String -> b) (eerr : b)
      -> b

open Parser

-------------------------------------------------------------------------------
-- Auxiliary types
-------------------------------------------------------------------------------

data Consumption : Set where
  consumed : Consumption
  empty : Consumption

data Result (a : Set) : Set where
  ok : a -> Result a
  err : Result a

data Reply (a : Set) : Set where
  reply : Consumption -> Result a -> Reply a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-Parser : Functor Parser
  Functor-Parser .map f p = toParser \ where
    s cok cerr eok eerr -> unParser p s (cok <<< f) cerr (eok <<< f) eerr

  Applicative-Parser : Applicative Parser
  Applicative-Parser .pure x = toParser \ where
    s _ _ eok _ -> eok x s
  Applicative-Parser ._<*>_ m k = toParser \ where
    s cok cerr eok eerr ->
      let
        mcok x s' = unParser k s' (cok <<< x) cerr (cok <<< x) cerr
        meok x s' = unParser k s' (cok <<< x) cerr (eok <<< x) eerr
      in
        unParser m s mcok cerr meok eerr

  Monad-Parser : Monad Parser
  Monad-Parser ._>>=_ m k = toParser \ where
    s cok cerr eok eerr ->
      let
        mcok x s' = unParser (k x) s' cok cerr cok cerr
        meok x s' = unParser (k x) s' cok cerr eok eerr
      in
        unParser m s mcok cerr meok eerr

  Alternative-Parser : Alternative Parser
  Alternative-Parser .azero = toParser \ where
    s _ _ _ eerr -> eerr
  Alternative-Parser ._<|>_ m n = toParser \ where
    s cok cerr eok eerr ->
      let
        meerr =
          let
            ncerr = cerr
            neok x s' = eok x s'
            neerr = eerr
          in
            unParser n s cok ncerr neok neerr
      in
        unParser m s cok cerr eok meerr

  Show-Consumption : Show Consumption
  Show-Consumption .showsPrec _ = \ where
    consumed -> showString "consumed"
    empty -> showString "empty"

  Show-Result : {{Show a}} -> Show (Result a)
  Show-Result .showsPrec _ err = showString "err"
  Show-Result .showsPrec prec (ok x) = showParen (prec > appPrec) $
    showString "ok " <<< showsPrec appPrec+1 x

  Show-Reply : {{Show a}} -> Show (Reply a)
  Show-Reply .showsPrec prec (reply consumption result) =
    showString "reply "
      <<< showsPrec prec consumption
      <<< showString " "
      <<< showsPrec prec result

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

try : Parser a -> Parser a
try p = toParser \ where
  s cok _ eok eerr ->
    let eerr' = eerr
    in unParser p s cok eerr' eok eerr'

notFollowedBy : Parser a -> Parser Unit
notFollowedBy p = toParser \ where
  s _ _ eok eerr ->
    let
      cok' _ _ = eerr
      cerr' = eok tt s
      eok' _ _ = eerr
      eerr' = eok tt s
    in
      unParser p s cok' cerr' eok' eerr'

option : a -> Parser a -> Parser a
option x p = p <|> pure x

many : Parser a -> Parser (List a)
many = fix \ where
  many p -> option [] (| p :: many p |)

many1 : Parser a -> Parser (List a)
many1 p = (| p :: many p |)

optional : Parser a -> Parser (Maybe a)
optional p = (| just p | nothing |)

choose : Parser a -> Parser b -> Parser (Either a b)
choose l r = (| left l | right r |)

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

prefix : (a -> b) -> Parser (b -> b) -> Parser a -> Parser b
prefix = fix \ where
  prefix wrap op p -> op <*> prefix wrap op p <|> wrap <$> p

postfix : (a -> b) -> Parser a -> Parser (b -> b) -> Parser b
postfix {a} {b} wrap p op = (| (wrap <$> p) # p' |)
  where
    p' : Parser (b -> b)
    p' = fix \ where
      p' -> option id (| op >>> p' |)

infixl1 : (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
infixl1 wrap p op = postfix wrap p (| flip op p |)

infixr1 : (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
infixr1 = fix \ where
  infixr1 wrap p op -> (| p # (| flip op (infixr1 wrap p op) |) <|> pure wrap |)

chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = infixl1 id

chainl : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op x = option x (chainl1 p op)

chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 = infixr1 id

chainr : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op x = option x (chainr1 p op)

-------------------------------------------------------------------------------
-- Char parsers
-------------------------------------------------------------------------------

satisfy : (Char -> Bool) -> Parser Char
satisfy test = toParser \ where
  s cok _ _ eerr ->
    if s == ""
      then eerr
      else
        let (c , s') = String.uncons s {{trustMe}}
        in if test c then cok c s' else eerr

anyChar : Parser Char
anyChar = satisfy (const true)

eof : Parser Unit
eof = notFollowedBy anyChar

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
alphaNum = satisfy Char.isAlphaNum

space : Parser Char
space = satisfy Char.isSpace

skipSpaces : Parser Unit
skipSpaces = skipMany space

newline : Parser Char
newline = char '\n'

crlf : Parser Char
crlf = char '\r' *> newline

endOfLine : Parser Char
endOfLine = try newline <|> crlf

tab : Parser Char
tab = char '\t'

-------------------------------------------------------------------------------
-- String parsers
-------------------------------------------------------------------------------

string : String -> Parser String
string = map String.pack <<< traverse char <<< String.unpack

word : Parser String
word = fix \ where
  word -> option "" (| String.cons alpha word |)

word1 : Parser String
word1 = (| String.cons alpha word |)

takeWhile : (Char -> Bool) -> Parser String
takeWhile p = toParser \ where
  s cok _ _ _ -> uncurry cok (String.break p s)

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
runParser p s =
  let
    cok x _ = just x
    cerr = nothing
    eok x _ = just x
    eerr = nothing
  in
    unParser p s cok cerr eok eerr

runParser' : Parser a -> String -> Reply a
runParser' p s =
  let
    cok x _ = reply consumed (ok x)
    cerr = reply consumed err
    eok x _ = reply empty (ok x)
    eerr = reply empty err
  in
    unParser p s cok cerr eok eerr
