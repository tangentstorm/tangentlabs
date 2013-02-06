

This is a test example from 
http://abstractabsurd.blogspot.com/2008/04/intro-to-sdl-with-haskell.html

compile with ghc --make sdltest


> import Prelude
> import Graphics.UI.SDL as SDL

> background = "background.bmp"
> hello = "hello.bmp"

> main = do
>   SDL.init [InitEverything]
>   setVideoMode 640 480 32 []
>   image <- loadBMP hello
>   back <- loadBMP background
>   screen <- getVideoSurface


And the two blitSurface commands to actually paint the contents of one surface
onto another. The arguments are the source surface, the clipping rectangle of
this surface, the target surface, and the rectangle to which you want to paint.
In both cases, Nothing represents the entire surface. That's why when painting
the background both rectangles are Nothing.

>   blitSurface back Nothing screen Nothing
>   blitSurface image Nothing screen (Just (Rect 180 140 0 0))
>   SDL.flip screen
>   quitHandler



> quitHandler :: IO ()
> quitHandler = do
>   e <- waitEvent
>   case e of
>     Quit -> return ()
>     otherwise -> do
>                  print e
>                  quitHandler
