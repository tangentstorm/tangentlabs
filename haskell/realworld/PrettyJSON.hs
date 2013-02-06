module PrettyJSON (renderJValue) where

import Numeric (showHex)
import Data.Char (ord)
import Data.Bits (shiftR, (.&.))
import SimpleJSON (JValue(..))
import Prettify (Doc, (<>), char, double, enclose,
                 fsep, hcat, punctuate, text, compact, pretty)



string :: String -> Doc
-----------------------
string = enclose '"' '"' . hcat . map oneChar

oneChar :: Char -> Doc
oneChar c = case lookup c simpleEscapes of
              Just r -> text r
              Nothing | mustEscape c -> hexEscape c
                      | otherwise    -> char c
    where mustEscape c = c < ' ' || c == '\x7f' || c > '\xff'


simpleEscapes :: [(Char, String)]
simpleEscapes = zipWith ch "\b\n\f\r\t\\\"/" "bnfrt\\\"/"
    where ch a b = (a, ['\\', b])


hexEscape :: Char -> Doc
hexEscape c | d < 0x10000 = smallHex d
            | otherwise   = astral (d - 0x10000)
    where d = ord c
            

smallHex :: Int -> Doc
smallHex x  = text "\\u"
           <> text (replicate (4 - length h) '0')
           <> text h
    where h = showHex x ""

astral :: Int -> Doc
astral n = smallHex (a + 0xD800) <> smallHex (b + 0xDC00)
    where a = (n `shiftR` 10) .&. 0x3FF
          b = n .&. 0x3FF



-- arrays and objects --


series :: Char -> Char -> (a -> Doc) -> [a] -> Doc
series open close item = enclose open close
                         . fsep . punctuate (char ',') . map item




renderJValue :: JValue -> Doc
--------------------------------
renderJValue (JString s) = string s
renderJValue (JNumber n) = double n
renderJValue (JBool True)  = text "true"
renderJValue (JBool False) = text "false"
renderJValue JNull         = text "null"

renderJValue (JArray arr) = series '[' ']' renderJValue arr

renderJValue (JObject ob) = series '{' '}' field ob
    where field (name, value) = string name <> text ": " <> renderJValue value






-- putJValue :: JValue -> IO ()
----------------------------
-- putJValue v = putStrLn (renderJValue v)


