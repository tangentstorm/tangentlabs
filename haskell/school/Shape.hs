
{- A shape module from SOE, chapter two -}

module Shape (Shape (Rectangle, Ellipse, RtTriangle, Polygon),
              Radius, Side, Vertex,
              square, circle, distBetween, area)
    where

data Shape = Rectangle Side Side
           | Ellipse Radius Radius
           | RtTriangle Side Side
           | Polygon [Vertex]
             deriving Show

type Radius = Float
type Side = Float
type Vertex = (Float, Float)

square s = Rectangle s s
circle r = Ellipse r r

area :: Shape -> Float
area (Rectangle s1 s2) = s1 * s2
area (RtTriangle s1 s2) = s1 * s2 / 2
area (Ellipse r1 r2) = pi * r1 * r2
area (Polygon (v1: vs)) = polyArea vs
      where polyArea :: [Vertex] -> Float
            polyArea (v2 : v3 : vs') = triArea v1 v2 v3
                                     + polyArea (v3:vs')
            polyArea _ = 0

triArea :: Vertex -> Vertex -> Vertex -> Float
triArea v1 v2 v3 = let a = distBetween v1 v2
                       b = distBetween v2 v3
                       c = distBetween v3 v1
                       s = (a + b + c) / 2
                   in sqrt (s * (s - a) * (s - b) * (s - c))

distBetween :: Vertex -> Vertex -> Float
distBetween (x1, y1) (x2, y2) =
    sqrt ((x1 - x2)^2 + (y1 - y2)^2)
