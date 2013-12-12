module Main where
-----------------------------------------------------------------
-- core tree datatype
-----------------------------------------------------------------

data Tree a
   = E                              -- empty node
   | L a                            -- leaf node
   | T (Tree a) a (Tree a)          -- inner tree node

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
rotr other               = other


-----------------------------------------------------------------
-- tree building
-----------------------------------------------------------------

balance :: Tree a -> Tree a
balance tree = tree
-------

cmp :: (Ord a) => a -> Tree a -> Ordering
---
cmp v (E) = EQ
cmp v (L x) = compare v x
cmp v (T p q r) = compare v q


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
-- main routine
-----------------------------------------------------------------

main :: IO ()
----
main = let avl = fromList [8,6,7,5,3,0,9] in print avl
