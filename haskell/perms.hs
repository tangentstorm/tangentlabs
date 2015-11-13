-- generate all permutations of a list
import Data.List

perms []  = []
perms [x] = [[x]]
perms xs  = concat [[ x:p | p <- perms (delete x xs) ] | x <- xs]

main = mapM_ (putStrLn.show) $ perms [0..5]
