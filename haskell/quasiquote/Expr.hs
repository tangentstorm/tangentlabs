{-# LANGUAGE DeriveDataTypeable #-}
module Expr {- (Expr(..),
             BinOp(..),
             eval,
             parseExpr) -}
    where

import Data.Generics
import Text.ParserCombinators.Parsec

data Expr = IntExpr Integer
          | AntiIntExpr String
          | BinopExpr BinOp Expr Expr
          | AntiExpr String
            deriving (Show, Typeable, Data)

data BinOp = AddOp
           | SubOp
           | MulOp
           | DivOp
             deriving (Show, Typeable, Data)

eval :: Expr -> Integer
eval (IntExpr n)        = n
eval (BinopExpr op x y) = (opToFun op) (eval x) (eval y)
    where
      opToFun AddOp = (+)
      opToFun SubOp = (-)
      opToFun MulOp = (*)
      opToFun DivOp = div


small = lower <|> char '_'
large = upper
idchar = small <|> large <|> digit <|> char '\''

lexeme p = do { x <- p; spaces; return x }
symbol name = lexeme (string name)
parens p = between (symbol "(") (symbol ")") p

expr :: CharParser st Expr
expr = term `chainl1` addop

term :: CharParser str Expr
term = factor `chainl1` mulop

factor :: CharParser st Expr
factor = parens expr <|> integer <|> try antiIntExpr <|> antiExpr

mulop =   do { symbol "*"; return $ BinopExpr MulOp }
      <|> do { symbol "/"; return $ BinopExpr DivOp }

addop =   do { symbol "+"; return $ BinopExpr AddOp }
      <|> do { symbol "-"; return $ BinopExpr SubOp }

integer :: CharParser st Expr
integer = lexeme $ do { ds <- many1 digit; return $ IntExpr (read ds) }

ident :: CharParser s String
ident = do { c <- small; cs <- many idchar; return (c:cs) }

antiIntExpr = lexeme $ do { symbol "$int:"; id <- ident; return $ AntiIntExpr id }
antiExpr = lexeme $ do { symbol "$"; id <- ident; return $ AntiExpr id }


parseExpr :: Monad m => (String, Int, Int) -> String -> m Expr
parseExpr (file, line, col) s = 
    case runParser p () "" s of
      Left err -> fail $ show err
      Right e  -> return e
    where
      p = do pos <- getPosition
             setPosition $
               (flip setSourceName) file $
               (flip setSourceLine) line $
               (flip setSourceColumn) col $
               pos
             spaces
             e <- expr
             eof
             return e
