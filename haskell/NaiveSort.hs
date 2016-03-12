-- i guess this is really a naive quicksort.
module NaiveSort where

nsort :: Ord a => [a] -> [a]
nsort [] = []
nsort [x] = [x]
nsort (x:xs) = (nsort $ filter (<x) xs)
            ++   x  : (filter (==x) xs)
            ++ (nsort $ filter (>x) xs)
