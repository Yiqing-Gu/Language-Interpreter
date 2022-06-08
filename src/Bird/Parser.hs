module Bird.Parser where

import Control.Monad
import Data.Char

--------------------------------------------------------------------------------

newtype Parser a = Parser (String -> [(a, String)])

runParser :: Parser a -> String -> [(a, String)]
runParser (Parser f) = f

parse :: Parser a -> String -> Maybe a
parse p s
    | null ps   = Nothing
    | otherwise = Just (fst (head ps))
    where ps = runParser p s

instance Functor Parser where
    fmap f p = Parser (\s -> [(f a, s') | (a, s') <- runParser p s])

instance Monad Parser where
    return a = Parser (\s -> [(a, s)])
    p >>= k  = Parser (\s -> concat [runParser (k a) s' | (a, s') <- runParser p s])

instance Applicative Parser where
    pure = return
    (<*>) = liftM2 ($)

--------------------------------------------------------------------------------

next :: Parser Char
next = Parser f
    where f [] = []
          f (c:cs) = [(c, cs)]

err :: Parser a
err = Parser f
    where f _ = []

(<\/>) :: Parser a -> Parser a -> Parser a
p <\/> q = Parser f
    where f s = runParser p s ++ runParser q s

(<|>) :: Parser a -> Parser a -> Parser a
p <|> q = Parser f
    where f s | null ps = qs
              | otherwise = ps
              where ps = runParser p s
                    qs = runParser q s

--------------------------------------------------------------------------------

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = do c <- next
               if p c
               then return c
               else err

char :: Char -> Parser ()
char c = do satisfy (c ==)
            return ()

string :: String -> Parser ()
string cs = mapM_ char cs

lower :: Parser Char
lower = satisfy isLower

upper :: Parser Char
upper = satisfy isUpper

digit :: Parser Int
digit = do d <- satisfy isDigit
           return (ord d - ord '0')

--------------------------------------------------------------------------------

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p sep = p >>= rest
    where rest x = (do f <- sep
                       y <- p
                       rest (f x y)) <|>
                   return x

many1 :: Parser a -> Parser [a]
many1 p = do x <- p
             xs <- many p
             return (x : xs)

option :: a -> Parser a -> Parser a
option x p = p <|> return x

many :: Parser a -> Parser [a]
many = option [] . many1

--------------------------------------------------------------------------------

spaces :: Parser String
spaces = many (satisfy isSpace)

token :: Parser a -> Parser a
token p = spaces >> p

symbol :: String -> Parser ()
symbol cs = token (string cs)

nat, natural :: Parser Int
nat = do ds <- many1 digit
         return (number (reverse ds))
    where number [] = 0
          number (d:ds) = d + 10 * number ds
natural = token nat

int :: Parser Int
int = token (do f <- option id (string "-" >> return negate)
                n <- nat
                return (f n))

--------------------------------------------------------------------------------

sepBy, sepBy1 :: Parser a -> Parser b -> Parser [b]
sepBy1 p q = do x <- q
                xs <- option [] (p >> sepBy p q)
                return (x : xs)
sepBy p q = option [] (sepBy1 p q)

surround :: Parser a -> Parser b -> Parser c -> Parser b
surround p q r = do p
                    x <- q
                    r
                    return x

parens, brackets :: Parser a -> Parser a
parens p = surround (symbol "(") p (symbol ")")
brackets p = surround (symbol "[") p (symbol "]")
