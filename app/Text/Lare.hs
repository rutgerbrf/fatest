{-# LANGUAGE LambdaCase #-}

module Text.Lare (RE (..), parseStr) where

import Control.Applicative (Alternative (empty, many, (<|>)))
import Control.Monad (MonadPlus (..))
import Data.Char (isAlpha)

newtype Parser a = Parser {parse :: String -> [(a, String)]}

runParser :: Parser a -> String -> Either String a
runParser m s =
  case parse m s of
    [(res, [])] -> Right res
    [(_, rs)] -> Left "parser did not consume entire stream"
    _ -> Left "parser error"

item :: Parser Char
item = Parser $ \case
  [] -> []
  (c : cs) -> [(c, cs)]

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p f = Parser $ \s -> concatMap (\(a, s') -> parse (f a) s') $ parse p s

unit :: a -> Parser a
unit a = Parser $ \s -> [(a, s)]

instance Functor Parser where
  fmap f (Parser cs) = Parser $ \s -> [(f a, b) | (a, b) <- cs s]

instance Applicative Parser where
  pure = unit
  (Parser cs1) <*> (Parser cs2) = Parser $ \s -> [(f a, s2) | (f, s1) <- cs1 s, (a, s2) <- cs2 s1]

instance Monad Parser where
  return = pure
  (>>=) = bind

instance MonadPlus Parser where
  mzero = failure
  mplus = combine

instance Alternative Parser where
  empty = mzero
  (<|>) = option

combine :: Parser a -> Parser a -> Parser a
combine p q = Parser $ \s -> parse p s ++ parse q s

failure :: Parser a
failure = Parser $ const []

option :: Parser a -> Parser a -> Parser a
option p q = Parser $ \s ->
  case parse p s of
    [] -> parse q s
    res -> res

satisfy :: (Char -> Bool) -> Parser Char
satisfy p =
  item >>= \c ->
    if p c
      then unit c
      else failure

oneOf :: [Char] -> Parser Char
oneOf s = satisfy (`elem` s)

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do
  a <- p
  rest a
  where
    rest a =
      ( do
          f <- op
          b <- p
          rest $ f a b
      )
        <|> return a

char :: Char -> Parser Char
char c = satisfy (c ==)

alpha :: Parser (RE Char)
alpha = REA <$> satisfy isAlpha

token :: Parser a -> Parser a
token p = do
  spaces
  a <- p
  spaces
  return a

string :: String -> Parser String
string [] = return []
string s@(c : cs) = do
  char c
  string cs
  return s

reserved :: String -> Parser String
reserved = token . string

spaces :: Parser String
spaces = many $ oneOf " \n\r\t"

parens :: Parser a -> Parser a
parens m = do
  reserved "("
  n <- m
  reserved ")"
  return n

zero :: Parser (RE Char)
zero = reserved "0" >> return RE0

one :: Parser (RE Char)
one = reserved "1" >> return RE1

expr :: Parser (RE Char)
expr = choice

choice :: Parser (RE Char)
choice = multiplication `chainl1` choiceOp

multiplication :: Parser (RE Char)
multiplication = quantification `chainl1` mulOp

quantification :: Parser (RE Char)
quantification =
  ( do
      val <- value
      reserved "*"
      return $ REK val
  )
    <|> value

value :: Parser (RE Char)
value = alpha <|> zero <|> one <|> parens expr

infixOp :: String -> (a -> a -> a) -> Parser (a -> a -> a)
infixOp x f = reserved x >> return f

choiceOp :: Parser (RE Char -> RE Char -> RE Char)
choiceOp = infixOp "+" REC

mulOp :: Parser (RE Char -> RE Char -> RE Char)
mulOp = spaces >> return RES
-- We don't have an explicit multiplication sign,
-- but spaces are allowed inbetween characters.

parseStr :: String -> Either String (RE Char)
parseStr = runParser expr

data RE a = RE0 | RE1 | REA a | REC (RE a) (RE a) | RES (RE a) (RE a) | REK (RE a)
  deriving (Show)
