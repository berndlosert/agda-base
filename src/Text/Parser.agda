{-# OPTIONS --type-in-type #-}

module Text.Parser where

private variable A B : Set

module Parser where

  open import Data.List
  open import Data.Char
  open import Data.Nat
  open import Data.String

  open import Prelude
    hiding (plus)

  record Parser (A : Set) : Set where
    constructor toParser
    field fromParser : String -> List (Pair A String)

  open Parser public

  instance
    functorParser : Functor Parser
    functorParser .map f p = toParser \ s ->
      map (cross f id) $ fromParser p s

    applicativeParser : Applicative Parser
    applicativeParser .pure x = toParser $ List.singleton <<< (x ,_)
    applicativeParser ._<*>_ f p = toParser \ s0 -> do
      (g , s1) <- fromParser f s0
      (x , s2) <- fromParser p s1
      return (g x , s2)

    monadParser : Monad Parser
    monadParser ._>>=_ p f = toParser \ s -> join $ do
      (v , s') <- (fromParser p s)
      return $ fromParser (f v) s'

    alternativeParser : Alternative Parser
    alternativeParser ._<|>_ p q =
      toParser \ s -> fromParser p s <> fromParser q s
    alternativeParser .empty = toParser $ const []

  -- item is a parser that consumes the first character if the input string is
  -- nonempty, and fails otherwise.
  item : Parser Char
  item = toParser (List.fromMaybe <<< String.uncons)

  -- first p is the parser whose output contains only the first successful
  -- parse (if it has one at all).
  first : Parser A -> Parser A
  first p = toParser \ s -> case (fromParser p s) of \ where
    [] -> []
    (x :: _) -> List.singleton x

  -- plus p q is just <> wrapped in first.
  plus : Parser A -> Parser A -> Parser A
  plus p q = first (p <|> q)

  -- satisfy takes a predicate, and yields a parser that consumes a single
  -- character if it satisfies the predicate, and fails otherwise.
  satisfy : (Char -> Bool) -> Parser Char
  satisfy p = do
    c <- item
    if p c then pure c else empty

  -- This combinator is used for creating single character parsers.
  char : Char -> Parser Char
  char c = satisfy (c ==_)

  -- Parse digits.
  digit : Parser Char
  digit = satisfy Char.isDigit

  -- Parse letters.
  letter : Parser Char
  letter = satisfy Char.isAlpha

  -- Parse lower-case characters.
  lower : Parser Char
  lower = satisfy Char.isLower

  -- Parser upper-case characters.
  upper : Parser Char
  upper = satisfy (\ c -> Char.isAlpha c && not (Char.isLower c))

  -- Parse alpha-numeric characters.
  alphanum : Parser Char
  alphanum = letter <|> digit

  -- Parse words.
  {-# TERMINATING #-}
  word : Parser String
  word = neword <|> (pure "")
    where
      neword : Parser String
      neword = do
        c <- letter
        s <- word
        return (String.cons c s)

  -- Produce string parsers.
  {-# TERMINATING #-}
  string : String -> Parser String
  string s with String.uncons s
  ... | nothing = pure ""
  ... | (just (c , s')) = char c >> string s' >> pure (String.cons c s')

  -- The combinator many (resp. many1) applies a parser p zero (resp. one) or
  -- more times to an input string. The results from each application of p are
  -- returned in a list.
  {-# TERMINATING #-}
  many : forall {x} -> Parser x -> Parser (List x)
  many1 : forall {x} -> Parser x -> Parser (List x)

  many p = plus (many1 p) (return [])
  many1 p = do
    x <- p
    xs <- many p
    return (x :: xs)

  -- This parses nonempty sequences of items separated by operators that
  -- associate to the left.
  {-# TERMINATING #-}
  chainl1 : Parser A -> Parser (A -> A -> A) -> Parser A
  chainl1 p op = p >>= rest
    where
      rest : _
      rest x = plus
        (op >>= \ f -> p >>= \ y -> rest (f x y))
        (return x)

  -- Parser for natural numbers.
  nat : Parser Nat
  nat = chainl1
      (digit >>= \ x -> return (Char.ord x - Char.ord '0'))
      (return (\ m n -> 10 * m + n))

  -- Spaces parser.
  spaces : Parser Unit
  spaces = do
    many1 (satisfy Char.isSpace)
    return unit

  -- Junk parser.
  junk : Parser Unit
  junk = do
    many spaces
    return unit

  -- Parser that skips junk.
  skip : Parser A -> Parser A
  skip p = junk >> p

  -- Consumes input as long as the predicate returns true, and return the
  -- consumed input.
  takeWhile : (Char -> Bool) -> Parser String
  takeWhile p = toParser \ s ->
    List.singleton (String.takeWhile p s , String.dropWhile p s)

  -- Consumes the rest of the input.
  takeRest : Parser String
  takeRest = takeWhile (const true)

  -- Run a parser on a string and get the first result.
  parse : Parser A -> String -> Maybe A
  parse p s with fromParser p s
  ... | [] = nothing
  ... | ((a , _) :: _) = just a

open Parser public
  using (Parser; toParser; fromParser)
  hiding (module Parser)
