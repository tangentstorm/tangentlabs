module Main where
import Test.HUnit

-----------------------------------------------------------------
-- core tree datatype
-----------------------------------------------------------------

data Bal = Lh | B | Rh          -- left heavy, balanced, right heavy
   deriving (Show, Eq)

data Tree a
   = E                          -- empty node
   | L a                        -- leaf node
   | T (Tree a) a (Tree a)      -- inner tree node

instance (Show a) => Show (Tree a) where
  show (E)       = "_"
  show (L x)     = show x
  show (T x y z) = foldl (++) "" ["(", (show x), " ", (show y), " ", (show z), ")"]

-----------------------------------------------------------------
-- tree rotations
-----------------------------------------------------------------


-- rotate left:  (p q (r s t))   -->  ((p q r) s t)
rotl :: Tree a -> Tree a
----
rotl (T p q (T r s t)) = (T (T p q r) s t)
rotl other = other


-- rotate right:  ((p q r) s t) --> (p q (r s t))
rotr :: Tree a -> Tree a
----
rotr (T (T p q r) s t) = (T p q (T r s t))
rotr other             = other

-----------------------------------------------------------------
-- queries
-----------------------------------------------------------------

height :: Tree a -> Int
------
height (E)       = 0
height (L _)     = 0
height (T p q r) = 1 + max (height p) (height r)


bal :: Tree a -> Bal
----------
bal (E)       = B
bal (L _)     = B
bal (T p _ q)
    | hp ==  hq = B
    | hp > hq+1 = Lh
    | hp+1 < hq = Rh
    | otherwise = B
    where hp = (height p)
          hq = (height q)

-----------------------------------------------------------------
-- tree building
-----------------------------------------------------------------

balance :: Tree a -> Tree a
-------
balance other = other


insert :: (Ord a) => Tree a -> a -> Tree a
------
insert (E) y = L y   {- empty nodes just become new leaves -}

insert (L x)  y      {- leaves become branches -}
     | y  < x = T (L y) x E
     | y == x = L x                     {- ignore duplicate entries -}
     | y  > x = T E y (L x)

insert (T p q r) y
     | y  < q  = balance $ T (insert p y) q r
     | y == q  = T p q r                {- again, ignore duplicates -}
     | y  > q  = balance $ T p q (insert r y)


fromList :: (Ord a) => [a] -> Tree a
--------
fromList xs = foldl insert E xs


-----------------------------------------------------------------
-- lookup
-----------------------------------------------------------------


-----------------------------------------------------------------
-- test suite
-----------------------------------------------------------------

h0 = E
h1 = T h0 E h0
h2 = T h1 E h1

test_height = TestCase ( do
     assertEqual "height h0" 0 $ height E
     assertEqual "height h1" 1 $ height h1
     assertEqual "height h2" 2 $ height h2
   )
test_bal = TestCase ( do
     assertEqual "bal (E)"     B $ bal E
     assertEqual "bal (L _)"   B $ bal $ L 1
     assertEqual "bal (E _ E)" B $ bal $ T E     2 (E)
     assertEqual "bal (E _ L)" B $ bal $ T E     2 (L 3)
     assertEqual "bal (L _ L)" B $ bal $ T (L 1) 2 (E)
     assertEqual "bal (L _ L)" B $ bal $ T (L 1) 2 (L 3)

     assertEqual "bal (h1 _ h0)" B  $ bal $ T h1 E h0
     assertEqual "bal (h2 _ h0)" Lh $ bal $ T h2 E h0
     assertEqual "bal (h0 _ h2)" Rh $ bal $ T h0 E h2
   )
tests = TestList [
    TestLabel "height"  test_height,
    TestLabel "balance" test_bal
  ]


-----------------------------------------------------------------
-- main routine
-----------------------------------------------------------------

main :: IO ()
----
main = do
  counts <- runTestTT tests
  print $ fromList [8,6,7,5,3,0,9]
  return ()
