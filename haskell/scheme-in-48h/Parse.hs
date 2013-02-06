module Parse where
import Control.Monad ( liftM )
import Text.ParserCombinators.Parsec hiding (spaces)

-- basic parser usage

symbol :: Parser Char
spaces :: Parser ()

symbol = oneOf "!#$%&|*+-/:<=>?@^_~"
spaces = skipMany1 space

-- a lisp parser -- 

type LispParser = Parser LispVal

data LispVal
  = Atom String
  | List [LispVal]
  | Dotted [LispVal] LispVal
  | Number Integer
  | String String
  | Bool Bool
  deriving Eq

parseString :: LispParser
parseString =
  do char '"'
     x <- many (noneOf "\"")
     char '"'
     return $ String x

parseAtom :: LispParser
parseAtom =
  do head <- letter <|> symbol
     tail <- many (letter <|> digit <|> symbol)
     let atom = head : tail 
     return $ case atom of
                "#t" -> Bool True
                "#f" -> Bool False
                _    -> Atom atom

-- another style of working with monads:
parseNumber :: LispParser
parseNumber = liftM (Number . read) $ many1 digit

-- and one with just the raw monad interface:
parseQuoted :: LispParser
parseQuoted =
  char '\'' >>
  parseExpr >>= \x -> 
  return $ List [Atom "quote", x]


parseList :: LispParser
parseList = liftM List $ sepBy parseExpr spaces

parseDotted :: LispParser
parseDotted =
  endBy parseExpr spaces           >>= \head ->
  char '.' >> spaces >> parseExpr  >>= \tail ->
  return $ Dotted head tail

parseExpr :: LispParser
parseExpr = 
      parseAtom
  <|> parseNumber
  <|> parseString
  <|> parseQuoted
  <|> do char '('
         x <- try parseList
              <|> parseDotted
         char ')'
         return x
