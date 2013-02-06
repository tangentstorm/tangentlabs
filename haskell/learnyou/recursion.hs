-- my versions of recursion stuff from learn you a haskell


mymax :: (Ord a) => [a] -> a
mymax [] = error "no mymax for empty list"
-- my version with helper function:
mymax (x:xs) = max' x xs
    where max' x [] = x
          max' x (y:ys) = max' (max x y) ys

-- simpler version from learn you a haskell:
mymax' [x] = x
mymax' (x:xs) = max x (mymax' xs)


replicate' :: Int -> a -> [a]
replicate' n x
    | n < 0     = error "can't replicate negative times"
    | n == 0    = []
    | otherwise = x : replicate' (n-1) x

mytake :: Int -> [a] -> [a]
mytake 0 _  = []
mytake _ [] = []
mytake n (x:ys) = x: mytake (n-1) ys


myzip :: [a] -> [b] -> [(a, b)]
myzip [] _ = []
myzip _ [] = []
myzip (a:as) (b:bs) = (a, b) : myzip as bs


myelem :: (Eq a) => a -> [a] -> Bool
myelem x []   = False
myelem x (y:ys) | x == y    = True
                | otherwise = myelem x ys
 

myquick :: (Ord a) => [a] -> [a]
myquick [] = []
myquick (x:xs) = myquick lesser ++ x : myquick greater
        where lesser  = [y | y <- xs, y <  x]
              greater = [y | y <- xs, y >= x]




