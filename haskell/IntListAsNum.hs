{-# Language FlexibleInstances, ConstraintKinds #-}
module IntListAsNum where

-- IntList :: Num implementation
--
-- At the GHCi prompt the expression  "take 5 10" yields
-- the strange error message:
--
--    No instance for (Num [a0]) arising from a use of ‘it’
--    In a stmt of an interactive GHCi command: print it
--
-- The implication here is that 'take x y' only works if you
-- can treat y as a list of items. That is, the type of 
-- (take 5) is [a0]->[a0]. 
--
-- The 10 doesn't match [a0], but haskell has the ability to 
-- cast integer literals to various types based on contex, 
-- /provided/  the type implements the 'Num' class, which
-- entails definining  fromInteger :: Integer -> a.
--
-- So what the the error message is teling us is that it has
-- no way to evaluate the expression, but it could, if we
-- implemented Num [a].
--
-- In this module, we'll do just that, for no particular reason
-- other than to prove that we can. :)

instance (Num a, Eq a) => Num [a] where

    -- We'll convert integers into a list of bits.
    fromInteger n
        | n <  0 = negate $ fromInteger (n * (-1))
        | n == 0 = [0]
        | n == 1 = [1]
        | n >  0 = (fromInteger rest) ++ (fromInteger bit)
                   where bit  = n `mod` 2
                         rest = (n-bit) `div` 2
    abs = id
    signum = const [1]
    negate = map (1-)
    (+) = braid (myOr)
    (*) = braid (myAnd)
    (-) = braid (myXor)



-- Since someone could manually add non-boolean integers to the
-- list, we'll just treat anything other than a 0 as a 1.

myOr :: (Num a, Eq a) => a -> a -> a
myOr 0 0 = 0
myOr 0 _ = 1
myOr _ 0 = 1
myOr _ _ = 1

myAnd :: (Num a, Eq a) => a -> a -> a
myAnd 0 0 = 0
myAnd 0 _ = 0
myAnd _ 0 = 0
myAnd _ _ = 1

myXor :: (Num a, Eq a) => a -> a -> a
myXor 0 0 = 0
myXor 0 _ = 1
myXor _ 0 = 1
myXor _ _ = 0


-- braid is like zipWith, but pads the shorter list first.
-- If either list is a single bit long, it uses that bit
-- throughout. Otherwise, it pads the shorter list with zeros.
braid :: (Num a) => (a->a->a) -> [a] -> [a] -> [a]
braid op xs ys
    | xl == yl  = zwop xs ys
    | xl == 1   = zwop (take yl $ cycle xs) ys
    | yl == 1   = zwop xs (take xl $ cycle ys)
    | xl < yl   = zwop ((take(yl-xl) os) ++ xs) ys
    | otherwise = braid (flip op) ys xs
    where xl=length xs; yl=length ys; zwop = (zipWith op); os=repeat 0



-- the final result:
--
-- *IntListAsNum> take 4 10
-- [1,0,1,0]

