{---------------------------------------------------------------
| a lexer for j, in haskell.
| j is a programming language from http://jsoftware.com/
+---------------------------------------------------------------
[ the zlib license ]

Copyright © 2014 Michal J. Wallace <http://tangentstorm.com>

This software is provided 'as-is', without any express or implied
warranty. In no event will the authors be held liable for any damages
arising from the use of this software.

Permission is granted to anyone to use this software for any purpose,
including commercial applications, and to alter it and redistribute it
freely, subject to the following restrictions:

   1. The origin of this software must not be misrepresented; you must not
   claim that you wrote the original software. If you use this software
   in a product, an acknowledgment in the product documentation would be
   appreciated but is not required.

   2. Altered source versions must be plainly marked as such, and must
   not be misrepresented as being the original software.

   3. This notice may not be removed or altered from any source
   distribution.
+---------------------------------------------------------------}
import Prelude hiding (lex)
import Data.Char (ord, chr)
import Test.HUnit


-- some types
type Chr = Char
type Str = [Chr]
type Bit = Bool

-- some constants
digit = ['0'..'9']
upper = ['A'..'Z']
lower = ['a'..'z']
alpha = upper ++ lower
alnum = alpha ++ ('_':digit)
jpunc = "=<>_+*-%^$~|.:,;#!/\\[]{}\"`@&?"


{-----------------------------------------------------------------
| split a string based on a predicate (allowing lookahead)
+-----------------------------------------------------------------}
data SplitRule = KeepL | KeepR | Drop

split :: SplitRule -> ([a] -> Bit) -> [a] -> ([a], [a])
split r f s = aux s []
    where
      aux [] acc = ((reverse acc),[])
      aux (x:xs) acc
          = if f (x:xs)
            then case r of
                   KeepL -> ((reverse (x:acc)), xs)
                   KeepR -> ((reverse acc), (x:xs))
                   Drop  -> ((reverse acc), xs)
            else aux xs (x:acc)


{---------------------------------------------------------------
| nxtok : fetch the next token from a string.
+---------------------------------------------------------------}
nxtok :: Str -> (Str, Str)
-- handle
niltok = ("","")
nxtok "" = niltok

-- skip whitespace, except for newlines
nxtok ('\n':s) = (['\n'], s)
nxtok (ws:s) | (ord ws) <= 32 = nxtok s

-- any 1-character string will be a token by itself.
nxtok (c:"") = ([c], "")
nxtok (c:h:"") = nxtok (c:h:"\0") -- pad with \0 so next case can do lookahead
nxtok (c:h:s)
    -- parens are their own tokens
    | c `elem` "()" = ([c], h:s)

    -- numbers / arrays
    -- todo : extended number notation (1r2, 16bff32, etc)
    | c `elem` digit
        = let (arr, more) = split KeepR (not.(`elem` ' ':digit).head) (h:s)
          in (unwords $ words (c:arr), more)

    -- strings
    | c == '\'' -- the 'f' below is matching "'" but not "''"
        = let f (x:xs) = (x=='\'') && ((xs/=[]) || ('\''==head xs))
              (str, more) = split KeepL f (h:s)
          in ((c:str), more)



-- ntok (c:h:s) , continued

    -- special case for "p.." and "&.:" primitives
    | (c:h:[(head s)] == "p..") = ("p..", tail s)
    | (c:h:[(head s)] == "&.:") = ("&.:", tail s)

    -- comments are also 3 chars but consume to end of line
    | (c:h:[(head s)] == "NB.")
        = let (toEOL, more) = split KeepR ((=='\n').head) (tail s)
          in ("NB." ++ toEOL, more)

    -- the other primitives are all 1 or 2 characters
    -- and the second one is always in ".:"
    | c `elem` jpunc
        = if h `elem` ".:"
          then (c:[h], s)     -- 2-char primitives
          else ([c], h:s)     -- 1-char primitives

    -- "letter" primitives
    | (h `elem` ".:") && (c `elem` alpha) = ((c:[h]), s)

    -- names
    | c `elem` alpha
        = let (tok, more) = split KeepL ((`elem`alpha).head) (h:s)
          in ((c:tok), more)



{---------------------------------------------------------------
| lex : tokenize a j source string
+---------------------------------------------------------------}

lex :: Str -> [Str]
lex "" = []
lex str = let (h, t) = nxtok str
          in if h == "" then lex t else (h : lex t)


{-----------------------------------------------------------------
| unit tests
+-----------------------------------------------------------------}
tests = TestList [
         TestLabel "arrays" test_arrays,
         TestLabel "spaces" test_spaces,
         TestLabel "comments" test_comments
        ]


checkLex :: Str -> [Str] -> Assertion
checkLex j toks = assertEqual j toks $ lex j


-- test cases

test_arrays = TestCase ( do
     checkLex "0" ["0"]
     checkLex "0 1" ["0 1"]
     checkLex "0 12" ["0 12"]
  )

test_symbols = TestCase ( do
     checkLex "+."   ["+"]
     checkLex "+"    ["+", "+."]
     checkLex "+.+:" ["+", "+.", "+:"]
  )

test_spaces = TestCase ( do
     checkLex "" []
     checkLex " " []
     checkLex "\t" []
     checkLex "    +" ["+"]
     checkLex "+    " ["+"]
     checkLex "(  )" ["(", ")"]
  )

test_comments = TestCase ( do
     assertEqual "start"  ["NB. comment"] $ lex "NB. comment"
     assertEqual "mixed"  ["NB. comment"] $ lex "NB. comment"
  )




{-----------------------------------------------------------------
| main
+-----------------------------------------------------------------}
main = runTestTT tests
