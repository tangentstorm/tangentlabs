module AVLTree where
-----------------------------------------------------------------
-- core tree datatype
-----------------------------------------------------------------

data Tree a = Nil | Leaf a | Node (Tree a) (Tree a)

instance (Show a) => Show (Tree a) where
  show Nil        = "_"
  show (Leaf x)   = (show x)
  show (Node x y) = "(" ++ (show x) ++ " " ++ (show y) ++ ")"

-----------------------------------------------------------------
-- tree rotations
-----------------------------------------------------------------

rotl :: Tree a -> Tree a
rotl (Node x (Node y z)) = Node (Node x y) z
rotl other               = other

rotr :: Tree a -> Tree a
rotr (Node (Node x y) z) = Node x (Node y z)
rotr other               = other

