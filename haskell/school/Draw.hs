
module Draw (inchToPixel, pixelToInch, intToFloat,
             xWin, yWin, trans, shapeToGraphic, spaceClose )
where

import Shape
import SimpleGraphics
import SOEGraphics

inchToPixel :: Float -> Int
inchToPixel x = round (100 * x)

pixelToInch :: Int -> Float
pixelToInch x = intToFloat x / 100

intToFloat :: Int -> Float
intToFloat n = fromInteger (toInteger n)

xWin,yWin :: Int
xWin = 600
yWin = 500


trans :: Vertex -> Point
trans (x,y) = (xWin2 + inchToPixel x,
               yWin2 - inchToPixel y)

xWin2, yWin2 :: Int
xWin2 = xWin `div` 2
yWin2 = yWin `div` 2


transList :: [Vertex] -> [Point]
transList [] = []
transList (p:ps) = trans p : transList ps


shapeToGraphic :: Shape -> Graphic
shapeToGraphic ( Rectangle s1 s2 )
    = let s12 = s1 / 2
          s22 = s2 / 2
      in polygon (transList 
                  [(-s12, -s22), (-s12,s22), (s12, s22), (s12, -s22)])

shapeToGraphic ( Ellipse r1 r2 )
    = ellipse ( trans ( -r1, -r2 )) (trans (r1, r2))

shapeToGraphic ( RtTriangle s1 s2 )
    = polygon ( transList [(0,0), (s1,0), (0,s2)])

shapeToGraphic ( Polygon vts )
    = polygon ( transList vts )


sh1 = Rectangle 3 2
sh2 = Ellipse 1 1.5
sh3 = RtTriangle 3 2
sh4 = Polygon [(-2.5,2.5), (-1.5,2.0), (-1.1,0.2),
               (-1.7,-1.0), (-3.0, 0)]

type ColoredShapes = [(Color, Shape)]
shs :: ColoredShapes
shs = [(Red, sh1), (Blue, sh2), (Yellow, sh3), (Magenta, sh4)]

drawShapes :: Window -> ColoredShapes -> IO ()
drawShapes w [] = return ()
drawShapes w ((c,s):cs) = do drawInWindow w ( withColor c (shapeToGraphic s))
                             drawShapes w cs

main0 =
    runGraphics (
        do w <- openWindow "Drawing Shapes" (xWin, yWin)           
           drawInWindow w ( withColor Red ( shapeToGraphic sh1 ))
           drawInWindow w ( withColor Blue ( shapeToGraphic sh2 ))
           spaceClose w )
                
main1 = runGraphics (
    do w <- openWindow "More shapes" (xWin, yWin)
       drawShapes w shs
       spaceClose w )

