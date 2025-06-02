module Data.String.Parser where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Char as Char using ()
open import Data.Monoid.Foldable
open import Data.List as List using ()
open import Data.String as String using ()
open import Data.Sequence
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type

-------------------------------------------------------------------------------
-- Auxiliary types
-------------------------------------------------------------------------------

data Consumption : Type where
  consumed : Consumption
  empty : Consumption

data Result (a : Type) : Type where
  ok : a -> Result a
  err : Result a

data Reply (a : Type) : Type where
  reply : Consumption -> Result a -> Reply a

-------------------------------------------------------------------------------
-- Parser
-------------------------------------------------------------------------------

abstract
  Parser : Type -> Type
  Parser a = forall {b} 
    -> String 
    -> (cok : a -> String -> b) (cerr : b)
    -> (eok : a -> String -> b) (eerr : b)
    -> b

-------------------------------------------------------------------------------
-- Primitive parsers
-------------------------------------------------------------------------------

  convert : (Char -> Maybe a) -> Parser a
  convert f = \ where
      s cok _ _ eerr -> case (String.uncons s) \ where
        nothing -> eerr
        (just (c , s1)) -> case (f c) \ where
          nothing -> eerr
          (just x) -> cok x s1

  -- Rewinds failure.
  try : Parser a -> Parser a
  try p = \ where
    s cok _ eok eerr ->
      let eerr1 = eerr
      in p s cok eerr1 eok eerr1

  -- Rewinds success.
  lookAhead : Parser a -> Parser a
  lookAhead p = \ where
    s cok cerr eok eerr ->
      let eok1 a _ = eok a s
      in p s eok1 cerr eok1 eerr

  -- Rewinds always.
  notFollowedBy : Parser a -> Parser Unit
  notFollowedBy p = \ where
    s _ _ eok eerr ->
      let
        cok1 _ _ = eerr
        cerr1 = eok tt s
        eok1 _ _ = eerr
        eerr1 = eok tt s
      in
        p s cok1 cerr1 eok1 eerr1

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
      p s cok cerr eok eerr

  runParser' : Parser a -> String -> Reply a
  runParser' p s =
    let
      cok x _ = reply consumed (ok x)
      cerr = reply consumed err
      eok x _ = reply empty (ok x)
      eerr = reply empty err
    in
      p s cok cerr eok eerr

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

  instance
    mutual
      Functor-Parser : Functor Parser
      Functor-Parser .map = liftM

      Applicative-Parser : Applicative Parser
      Applicative-Parser ._<*>_ = ap
      Applicative-Parser .pure x = \ where
        s _ _ eok _ -> eok x s

      Monad-Parser : Monad Parser
      Monad-Parser ._>>=_ m k = \ where
        s cok cerr eok eerr ->
          let
            mcok x s1 = (k x) s1 cok cerr cok cerr
            meok x s1 = (k x) s1 cok cerr eok eerr
          in
            m s mcok cerr meok eerr

    Alternative-Parser : Alternative Parser
    Alternative-Parser .azero = \ where
      s _ _ _ eerr -> eerr
    Alternative-Parser ._<|>_ m n = \ where
      s cok cerr eok eerr ->
        let
          meerr =
            let
              ncerr = cerr
              neok x s1 = eok x s1
              neerr = eerr
            in
              n s cok ncerr neok neerr
        in
          m s cok cerr eok meerr

instance
  Semigroup-Parser : {{Semigroup a}} -> Semigroup (Parser a)
  Semigroup-Parser ._<>_ p q = (| p <> q |)

  Monoid-Parser : {{Monoid a}} -> Monoid (Parser a)
  Monoid-Parser .mempty = pure mempty 

  Show-Consumption : Show Consumption
  Show-Consumption .show = showDefault
  Show-Consumption .showsPrec _ = \ where
    consumed -> "consumed"
    empty -> "empty"

  Show-Result : {{Show a}} -> Show (Result a)
  Show-Result .show = showDefault
  Show-Result .showsPrec prec = \ where
    err -> "err"
    (ok x) -> showsUnaryWith showsPrec "ok" prec x

  Show-Reply : {{Show a}} -> Show (Reply a)
  Show-Reply .show = showDefault
  Show-Reply .showsPrec prec (reply consumption result) =
    showsBinaryWith showsPrec showsPrec "reply" prec consumption result  

-------------------------------------------------------------------------------
-- Alternative combinators
-------------------------------------------------------------------------------

option : a -> Parser a -> Parser a
option x p = p <|> pure x

many : Parser a -> Parser (List a)
many p = option [] (| p :: many p |)

many1 : Parser a -> Parser (List a)
many1 p = (| p :: many p |)

manyTill : Parser a -> Parser b -> Parser (List a)
manyTill p q = ([] <$ q) <|> (| p :: manyTill p q |)

optional : Parser a -> Parser (Maybe a)
optional p = (| just p | nothing |)

choose : Parser a -> Parser b -> Parser (Either a b)
choose l r = (| left l | right r |)

choice : List (Parser a) -> Parser a
choice = asum

exactly : Nat -> Parser a -> Parser (List a)
exactly 0 p = pure []
exactly n p = sequence (List.replicate n p)

between : Parser a -> Parser b -> Parser c -> Parser c
between l r p = l *> p <* r

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
prefix wrap op p = op <*> prefix wrap op p <|> wrap <$> p

postfix : (a -> b) -> Parser a -> Parser (b -> b) -> Parser b
postfix {a} {b} wrap p op = (| (wrap <$> p) & q |)
  where
    q : Parser (b -> b)
    q = option id (| op >>> q |)

infixl1 : (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
infixl1 wrap p op = postfix wrap p (| flip op p |)

infixr1 : (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
infixr1 wrap p op = (| p & (| flip op (infixr1 wrap p op) |) <|> pure wrap |)

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
satisfy f = convert \ where
  c -> if f c then just c else nothing

anyChar : Parser Char
anyChar = satisfy (const true)

eof : Parser Unit
eof = notFollowedBy anyChar

skipWhile : (Char -> Bool) -> Parser Unit
skipWhile f = skipMany (satisfy f)

skipAll : Parser Unit
skipAll = skipWhile (const true)

char : Char -> Parser Char
char c = satisfy (c ==_)

oneOf : List Char -> Parser Char
oneOf = satisfy <<< flip elem

noneOf : List Char -> Parser Char
noneOf = satisfy <<< flip notElem

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

spaces : Parser Unit
spaces = skipMany space

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
word = option "" (| String.cons alpha word |)

word1 : Parser String
word1 = (| String.cons alpha word |)

takeWhile : (Char -> Bool) -> Parser String
takeWhile f = String.pack <$> many (satisfy f)

takeAll : Parser String
takeAll = takeWhile (const true)

-------------------------------------------------------------------------------
-- Parser for numbers
-------------------------------------------------------------------------------

nat : Parser Nat
nat = chainl1 (convert Char.toDigit) (pure \ m n -> 10 * m + n)

int : Parser Int
int = (| neg (char '-' *> nat) | pos (char '+' *> nat) | pos nat |)

-------------------------------------------------------------------------------
-- Misc. parsers
-------------------------------------------------------------------------------

fully : Parser a -> Parser a
fully = between spaces eof

lexeme : Parser a -> Parser a
lexeme m = m <* spaces

symbol : String -> Parser String
symbol = lexeme <<< string

token : Parser a -> Parser a
token = lexeme <<< try

keyword : String -> Parser Unit
keyword s = token (string s *> notFollowedBy alphaNum)