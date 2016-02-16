-- apply a differen function depending on whether x is negative, 0, or positive

nzp :: (Int->a) -> (Int->a) -> (Int->a) -> Int -> a
nzp n z p x
    | x < 0 = n x
    | x ==0 = z x
    | x > 0 = p x

main :: IO ()
main = putStrLn $ map (nzp (const '-') (const '0') (const '+')) [-10..10]