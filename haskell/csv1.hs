-- rwh chapter 16
import Text.ParserCombinators.Parsec

{- a CSV file contains 0 or mor lines, each terminated by eol
 (and then the file itself is terminated by eof) -}
csvFile :: GenParser Char st [[String]]
csvFile = do
  result <- many line
  eof
  return result

-- each line has 1 or more cells, separated by a comma
line :: GenParser Char st [String]
line = do
  result <- cells
  eol
  return result

-- build up a list of cells
cells :: GenParser Char st [String]
cells = do
  first <- cellContent
  next <- remainingCells
  return (first : next)

-- cell either ends with a comma, indicating more cells follow
-- or not, indicating we're done with the line
remainingCells :: GenParser Char st [String]
remainingCells =
  (char ',' >> cells)  -- comma, so more cells coming
  <|> (return [])      -- no comma, so stop the coroutine


cellContent :: GenParser Char st String
cellContent =
    many (noneOf ",\n")

eol :: GenParser Char st Char
eol = char '\n'

parseCSV :: String -> Either ParseError [[String]]
parseCSV input = parse csvFile "(unknown)" input



