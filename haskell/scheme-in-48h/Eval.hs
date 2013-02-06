module Eval where
import Parse
import Text.PrettyPrint

-- | I decided to use Text.PrettyPrint instead of the example code.
instance Show LispVal where
  show = show . emit

emit :: LispVal -> Doc
emit v = case v of
  String x      -> doubleQuotes $ text x
  Atom   x      -> text x
  Number x      -> text $ show x
  Bool True     -> text "#t"
  Bool False    -> text "#f"
  List x@(h:t)  -> 
    if h == Atom "quote" 
      then hcat $ char '\'' : map emit t
      else parens $ hsep $ map emit x
