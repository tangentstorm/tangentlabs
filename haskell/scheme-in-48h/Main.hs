module  Main where
import System.Environment
import Text.ParserCombinators.Parsec hiding (spaces)
import Parse
import Eval

readExpr :: Show a => String -> Parser a -> String
readExpr input parser = 
  case parse parser "lisp" input of
    Left err -> "No match: " ++ show err
    Right ex -> "Found value: " ++ show ex

run :: Show a => Parser a -> IO ()
run parser =
   do args <- getArgs
      putStrLn $ readExpr (args !! 0) parser


main'0 = run (spaces >> symbol)

main'1 = run parseExpr

main = main'1
