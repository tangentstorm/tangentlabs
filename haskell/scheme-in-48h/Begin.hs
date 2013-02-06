module Main where
import System.Environment

main' :: IO ()
main' = do
  args <- getArgs
  putStrLn ("Hello, " ++ args !! 0)


main :: IO ()
main = do
  args <- getArgs
  if length args > 0 
    then putStrLn ("hello, " ++ args !! 0)
    else putStrLn "Hello."

