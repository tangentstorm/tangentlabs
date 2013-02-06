-- chapter 4 of real world haskell

import System.Environment (getArgs)

import Data.Char (digitToInt) -- we'll need ord shortly

asInt :: String -> Int


interactWith function inputFile outputFile = do
  input <- readFile inputFile
  writeFile outputFile (function input)

main = mainWith myFunction
    where mainWith f = do
            args <- getArgs
            case args of
              [input, output] -> interactWith f input output
              _ -> putStrLn "errer: exactly two arguments needed"
          myFunction = id


splitLines :: String -> [String]
splitLines [] = []
splitLines cs =
    let (pre, suf) = break isLineTerminator cs
    in pre : case suf of
               ('\r':'\n':rest) -> splitLines rest
               ('\r':rest) -> splitLines rest
               ('\n':rest) -> splitLines rest
               _ -> []

isLineTerminator c = c == '\r' || c == '\n'



fixLines :: String -> String
fixLines input = unlines (splitLines input)

asInt ints = loop 0 ints
    where loop acc [] = acc
          loop acc (x:xs) = loop acc' xs
              where acc' = acc * 10 + digitToInt x
                           