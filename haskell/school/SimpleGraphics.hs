module SimpleGraphics (spaceClose)
where
import SOEGraphics


spaceClose :: Window -> IO ()
spaceClose w 
    = do k <- getKey w         
         if k==' ' then closeWindow w
                   else spaceClose w

main1 = 
    runGraphics ( 
       do w <- openWindow 
               "My First Graphics Program" (300,300)
          drawInWindow w (text (100,200) "Hello Graphics World")
          spaceClose w )

----------------------

pic1 = withColor Green (ellipse (150, 150) (300, 200))
pic2 = withColor Blue (polyline [(100,50), (200, 50),
                                 (200, 250), (100,250), (100, 50)])

main2 =
    runGraphics (
    do w <- openWindow "Some Graphics Figures" (300, 300)
       drawInWindow w pic1       
       drawInWindow w pic2
       spaceClose w
    )


---------------------------

fillTri :: Window -> Int -> Int -> Int -> IO ()
fillTri w x y size
        = fillTriC w x y size Blue
fillTriC w x y size color
        = drawInWindow w ( withColor color
              ( polygon [(x,y), (x+size, y), (x, y-size), (x,y)]))

minSize :: Int
minSize = 8

sierpinskiTri :: Window -> Int -> Int -> Int -> IO ()
sierpinskiTri w x y size
              = if size <= minSize
                then fillTri w x y size
                else let size2 = size `div` 2
                     in do sierpinskiTri w x y size2
                           sierpinskiTri w x (y-size2) size2
                           sierpinskiTri w (x+size2) y size2

main3 =
    runGraphics (
        do w <- openWindow "Sierpinski's Triangle" (400, 400)
           sierpinskiTri w 50 300 256
           spaceClose w )

----------------------------
{- exercise : snowflake --}

{-

Okay, if you have an equilateral triangle with sides
of length 1, and you fold it in half, you have two 
right triangles, with sides: 1, b, and 2. 

0.25 + b^2 = 1
b^2 = 0.75
b = sqrt 0.75
-}


type APoint = (Float, Float)

--drawRegPoly :: Window -> Int -> Int -> Int -> Int -> Color
drawRegPoly w sides x y r color
    = drawInWindow w (withColor color ( polygon ( 
         simply ( move x y (scale r (regPoly sides ))))))

--simply :: [APoint] -> [Point]
simply vs = [(round x, round y) | (x,y) <- vs]

--move :: Float -> Float -> [APoint] -> [APoint]
move dx dy vs = [(x + dx, y + dy) | (x,y) <- vs]

--scale :: Float -> [APoint] -> [APoint]
scale size vs = [(x * size, y * size) | (x,y) <-  vs]

--regPoly :: Float -> [APoint]
regPoly sides = [ circPoint ( n * 2 * pi / sides )
                      | n  <- ([0..sides-1]++[0]) ]

--circPoint :: Float -> APoint
circPoint theta = (x, y) 
    where x = sin theta     -- sin t = opp/hyp ; hyp = 1
          y = cos theta     -- cos t = adj/hyp ; hyp = 1


--drawSnowFlake :: Window -> Int -> Int -> Float  -> IO ()
drawSnowFlake w x y size
    = do drawRegPoly w 5 x y size Red
         drawRegPoly w 5 x y (-size) Black

snowFlake =
    runGraphics (
        do w <- openWindow "snowflake" (400, 400)
           drawSnowFlake w 200 200 150.0
           spaceClose w )
           
