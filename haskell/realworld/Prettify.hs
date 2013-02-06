module Prettify
    ( Doc, empty, char, text, double
    , (<>)
    , fsep
    , compact
    , hcat, punctuate, pretty
    , enclose
    ) where

import SimpleJSON
import Numeric
import Data.Bits

data Doc = Empty
         | Char Char
         | Text String
         | Line
         | Concat Doc Doc
         | Union Doc Doc
           deriving (Show, Eq)


empty :: Doc
empty = Empty

char :: Char -> Doc
char c = Char c

text :: String -> Doc
text "" = Empty
text s  = Text s

double :: Double -> Doc
double d = text (show  d)

line :: Doc
line = Line

enclose :: Char -> Char -> Doc -> Doc
enclose left right x = char left <> x <> char right

(<>) :: Doc -> Doc -> Doc
Empty <> y = y
x <> Empty = x
x <> y     = x `Concat` y


hcat :: [Doc] -> Doc
hcat = foldr (<>) empty


fsep :: [Doc] -> Doc
fsep = foldr (</>) empty

(</>) :: Doc -> Doc -> Doc
x </> y = x <> softline <> y

softline :: Doc
softline = group line


group :: Doc -> Doc
group x = Union (flatten x) x

-- lazy evaluation! how awesome!
flatten :: Doc -> Doc
flatten (Concat x y) = Concat (flatten x) (flatten y)
flatten Line         = Char ' '
flatten (Union x _)  = flatten x
flatten other        = other 


punctuate :: Doc -> [Doc] -> [Doc]
punctuate p []      = []
punctuate p [d]     = [d]
punctuate p (d:ds)  = (d <> p) : punctuate p ds


compact :: Doc -> String
------------------------
compact x = transform [x]
    where transform [] = ""
          transform (d:ds) =
              case d of
                Empty      -> transform ds
                Char  c    -> c : transform ds
                Text  s    -> s ++ transform ds
                Line       -> '\n' : transform ds
                Concat a b -> transform (a:b:ds)
                Union  _ b -> transform (b:ds) -- always use the short version



pretty :: Int -> Doc -> String
------------------------------
pretty width x = best 0 [x]
    where best col (d:ds) = 
              case d of
                Empty      -> best col ds
                Char c     -> c : best (col + 1) ds
                Text s     -> s ++ best (col + length s) ds
                Line       -> '\n' : best 0 ds
                Concat a b -> best col (a:b:ds)
                Union a b  -> nicest col (best col (a:ds))
                                         (best col (b:ds))
          best _ _  = ""
          nicest col a b | a `fits` (width - least) = a
                         | otherwise = b
                         where least = min width col

-- i don't know why they put it the other way around..
fits :: String -> Int -> Bool
fits _        w | w < 0 = False
fits ""       w = True
fits ('\n':_) w = True
fits (c:cs)   w = cs `fits` (w - 1)
