NB. grammmar combinators for j
NB. --------------------------

NB. Pattern Matchers :: (bit num) <- ptn v str
NB. ------------------------------------------------
NB. bit indicates a match. num indicates the length.


NB. match results:
null =: (1 0)     NB. null: return 1 without consuming input
fail =: (0 0)     NB. fail: return 0 and consume nothing.
take =: 1 , ]     NB. take n : return true and consume n symbols

when =: 2 : 0     NB. u when v
:
  if. x (4 : v) y do. ".m else. fail end.
)

NB. primitive matchers
NB. --------------------------------------------------

NB. nul: match but do not consume
nul_match =: null"_

NB. sym: match a specific character or symbol
sym_match =: 'take 1' when 'x = {. y'

NB. lit: match a literal string
lit_match =: 'take #x' when 'x -: (i. # x) { y'

NB. any : match any of the items in x
any_match =: 'take 1' when 'x e.~ {. y'

NB. abstract syntax tree for grammars
NB. ------------------------------------------------------
jsyms=: 3 : '(":s) =: s: s=.'' '',y'

NB. these will reference their own names as symbols
tags =: jsyms 'seq opt rep alt def sub'


NB. grammar interpreter
NB. ------------------------------------------------------
rep =: (s:' rep')"_  ; ]

NB. { regular expression support }
NB. seq ::  [gram] -> bit
NB. opt ::  gram  -> bit    (like regexp '?')
NB. rep ::  gram  -> bit    (like '*')
NB. alt :: [gram] -> bit    (like "|")

NB. { recursion support, for context-free grammars }
NB. sub :: iden -> boolean;


NB. first characters match:
NB. we want to apply {. (head) to both x and y,
NB. then test with  = (equal) or -: (match)
NB. (f x) g (f y)  <--> x f &: g y
mch0 =: -:&:{.

NB. match repeating characters at the start of a string.
(0: i.~ {. = ]) 'aaabbcddeeea'

test =: 3 : 0
  assert (1 0) =       nul_match 'cat'
  assert (1 1) = 'c'   sym_match 'cat'
  assert (0 0) = 'a'   sym_match 'cat'
  assert (1 1) = 'abc' any_match 'cat'
  assert (1 3) = 'cat' lit_match 'catacomb'
  assert (0 0) = 'bat' lit_match 'catacomb'
  echo 'ok!'
)
test''
