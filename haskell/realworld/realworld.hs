


-- stuff from "rea world haskell"

add a b = a + b
sub a b = a - b
xor p q = (p && (not q)) || (q && (not p))

myDrop n xs = if n <= 0 || null xs
              then xs
              else myDrop (n - 1) (tail xs)

lastButOne xs = if length xs == 2 then head xs
                else if length xs < 2 then error "your list is too short"
                else lastButOne (tail xs)


-- here we're defining a type, BookInfo with one
-- constructor. ex:    Book 123 "name" ["author"]

data BookInfo = Book Int String [String]
                deriving (Show)


-- and another. even though the shapes are the same, the types are distinct

data MagazineInfo = Magazine Int String [String]
                    deriving (Show)

myInfo = Book 9780135072455 "Algebra of Programming"
         ["Richard Bird", "Oege de Moor"]




type CustomerID = Int
type ReviewBody = String

data BookReview = BookReview BookInfo CustomerID String
data BetterReview = BetterReview BookInfo CustomerID ReviewBody
type BookRecord = (BookInfo, BookReview)


data Bool = False | True
type Address = String

data Customer = Customer {
      customer_id :: CustomerID,
      name :: String,
      address :: Address }
                deriving (Show)


