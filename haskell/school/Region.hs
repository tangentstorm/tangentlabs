
module Region (Region (Shape, Translate, Scale, Complement, 
                       Union, Intersect, Empty),
               Coordinate,
               containsS, containsR,
               module Shape)
    where 
      
import Shape


type Coordinate = (Float, Float)
type Vector = (Float, Float)

-- a Region is either:
data Region = Shape Shape
            | Translate Vector Region -- translated region
            | Scale Vector Region -- scaled region
            | Complement Region
            | Region `Union` Region
            | Region `Intersect` Region
            | Empty
              deriving Show

               
infixr 5 `Union`
infixr 6 `Intersect`

-----

containsR :: Region -> Coordinate -> Bool

(Shape s) `containsR` p
    = s `containsS` p

(Translate (u, v) r) `containsR` (x,y)
    = r `containsR` (x - u, y-v)

(Scale (u, v) r) `containsR` (x,y)
    = r `containsR` (x/u, y/v)

(Complement r) `containsR` p
    = not (r `containsR` p)

(r1 `Union` r2) `containsR` p
    = r1 `containsR` p || r2 `containsR` p

(r1 `Intersect` r2) `containsR` p
    = r1 `containsR` p && r2 `containsR` p

Empty `containsR` p
    = False

------------

containsS :: Shape -> Coordinate -> Bool

(Rectangle s1 s2) `containsS` (x,y)
    = let s12 = s1/2
          s22 = s2/2
      in (-s1 <= x) && (x <= s1) && (-s22 <= y) && (y <=s22)

(Ellipse r1 r2) `containsS` (x,y)
    = (x/r1)^2 + (y/r2)^2 <= 1

(Polygon pts) `containsS` p
    = let leftOfList = map (isLeftOf p)
                       (zip pts
                            (tail pts ++ [head pts]))
          in and leftOfList

(RtTriangle s1 s2) `containsS` p
    = (Polygon [(0,0), (s1,0), (0, s2)]) `containsS` p
       
       
--------
isLeftOf :: Coordinate -> Ray -> Bool
(px, py) `isLeftOf` ((ax, ay), (bx, by))
    = let (s,t) = (px - ax, py - ay)
          (u,v) = (px - bx, py - by)
      in s * v >= t * u
type Ray = (Coordinate, Coordinate)
