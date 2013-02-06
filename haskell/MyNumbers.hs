
data Tally = Tally [Char]
             deriving (Show, Eq)

tally :: [Char] -> Tally
tally dots | all (== '.') dots = Tally dots
           | otherwise = error "just use dots!"

tallyFromInt :: Integer -> Tally
tallyFromInt i | i >= 0    = Tally (take j (repeat '.'))
               | otherwise = Tally ""
               where j = fromIntegral i

plus :: Tally -> Tally -> Tally
plus (Tally x) (Tally y) = Tally (x ++ y)

minus :: Tally -> Tally -> Tally
minus (Tally x) (Tally y) = Tally (drop (length x) y)

instance Num Tally where

    abs (Tally "")  = 0
    abs t           = t

    (+) = plus
    (-) = minus

    fromInteger = tallyFromInt
