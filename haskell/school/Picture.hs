
module Picture where

import Draw
import Region
import SOEGraphics hiding (Region)
import SOEGraphics qualified as G (Region)

data Picture = Region Color Region
             | Picture `Over` Picture
             | EmptyPic
               deriving Show

data Color = Black | Blue | Green | Cyan 
           | Red | Magenta | Yellow | White

