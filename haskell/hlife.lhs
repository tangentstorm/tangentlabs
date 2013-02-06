via: http://rosettacode.org/wiki/Conway's_Game_of_Life#Haskell

> import Data.Array
> import System.Console.ANSI
> import Control.Concurrent

> type Grid = Array Int Bool

> life :: Int -> Int -> Grid -> Grid
> life w h old =
>   listArray (bounds old) (map f coords)
>   where
>     coords = [(x, y) | y <- [0 .. h-1], x <- [0 .. w-1]]
>     f (x, y) | c && (n == 2 || n == 3) = True
>              | not c && n == 3 = True
>              | otherwise = False
>              where c = get x y
>                    n = count [get (x + x') (y + y')
>                                   | x' <- [-1, 0, 1]
>                                   , y' <- [-1, 0, 1]
>                                   , not (x' == 0 && y' == 0)]
>     get x y | x < 0 || x == w = False
>             | y < 0 || y == h = False
>             | otherwise       = old ! (x + y * w)

> count :: [Bool] -> Int
> count []           = 0
> count (False : xs) = 0 + count xs
> count (True : xs)  = 1 + count xs

> grid :: [String] -> (Int, Int, Grid)
> grid xs = (width, height, a)
>   where (width, height) = (length $ head xs, length xs)
>         a = listArray (0, width * height - 1) $ concatMap f xs
>         f = map g
>         g '.' = False
>         g _   = True


> printGrid :: Int -> Grid -> IO ()
> printGrid width = mapM_ f . split width . elems
>   where f []    = putStrLn ""
>         f (c:cs)= do
>                      setFg (if c then Green else Blue)
>                      putStr $ [g c]
>                      f cs
>         g False = '.'
>         g _     = '#'


> setFg x = setSGR [SetColor Foreground Vivid x]


> split :: Int -> [a] -> [[a]]
> split _ [] = []
> split n l  = a : split n b
>   where (a, b) = splitAt n l
 
> blinker = grid
>    [".#.",
>     ".#.",
>     ".#."]
 
> glider = grid
>   ["............",
>    "............",
>    "............",
>    ".......###..",
>    ".......#....",
>    "........#...",
>    "............"]
 
> printLife :: Int -> (Int, Int, Grid) -> IO ThreadId
> printLife n (w, h, g) = 
>   do
>     forkIO (mapM_ f $ take n $ iterate (life w h) g)
>   where f g = do
>             clearScreen
>             setCursorPosition 0 0
>             setFg White
>             putStrLn "------------------------------"
>             printGrid w g
>             setFg White
>             putStrLn "------------------------------"
>             threadDelay 1000000
>             setSGR [Reset]
>             -- setSGR [SetColor Foreground Dull White]
> main = printLife 10 glider
