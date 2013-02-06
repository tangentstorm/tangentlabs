
-- by abe egnor
-- http://www.mail-archive.com/haskell@haskell.org/msg12446.html

import Data.Array.IArray
import Data.Array.Unboxed
import Data.Ix
import System.Random

type Grid = UArray (Int, Int) Int

randomGrid :: (RandomGen g) => g -> Int -> Grid
randomGrid g s = listArray b $ map (\x -> if x then 1 else 0) $ take (rangeSize b) $ randoms g
  where b = ((0,0),(s-1,s-1))

getCell :: Grid -> (Int, Int) -> Int
getCell g c@(x,y) = if (x < xmin) || (x > xmax) || (y < ymin) || (y >= ymax) then 0 else g ! c
  where ((xmin, ymin), (xmax, ymax)) = bounds g

update :: Grid -> Grid
update g = array (bounds g) $ map aux $ assocs g
  where aux (c@(x,y),e) = let around = map (getCell g) $ filter (/= (x,y)) $ range ((x-1,y-1),(x+1,y+1))
                          in (c,rule (sum around) e)
        rule 2 e = e
        rule 3 e = 1
        rule _ _ = 0

printGrid :: Grid -> IO ()
printGrid g = do let ((xmin, ymin), (xmax, ymax)) = bounds g
                 mapM_ aux $ map (\x -> range ((x,ymin),(x,ymax))) [xmin..xmax]
                 putStrLn ""
  where aux ixs = do mapM_ (putStr . show) $ map (g!) ixs
                     putStrLn ""

main :: IO ()
main = printGrid $ (iterate update (randomGrid (mkStdGen 0) 50)) !! 100
