sym =: [: s: <   NB. symbol from string
str =:    5& s:  NB. string from symbol
lex =: [: s: ;:  NB. symbols from j words in string
ord =: a. i. ]
chr =: ord inv
swc =: <[:sym]

parser =: (0 : 0)
   0   1   2   3   4      5   6   7   8   9
  'nul lit any not eof'  'alt seq rep opt orp'
   10  11  12  13  14     15   16   17   18   19
  'def ref act tok skp'  'node hide lift keep virt'
)

tables =: (0 : 0)
[ up  pas ] NB. wejal -> pascal macros
  ar  'array'
  bg  'begin'
  cl  'class'
  co  'const'
  dy  '(x,y:ot):ot; inline; begin $re'
  en  'end;'
  fc  'interface'
  fn  'function'
  dy  '(x,y:vt):vt;'
  mo  '(y:vt):vt;'
  mo  '$ismo inline; begin $re'
  pc  'procedure'
  pg  'program'
  rc  'record'
  re  'result :='
  ty  'type'
  va  'var'
  vt  'variant'
  wl  'writeln'

[ up  pas ] NB. monadic verbs
  m   '- y'
  n   '1-y'
  p1  'y+1'
  m1  'y-1'
  t2  'y*2'
# ce  'ceil(y)'
# fl  'floor(y)'

[ up pas ] NB. dyadic verbs
  eq  'x =  y'
  ne  'x <> y'
  lt  'x <  y'
  gt  'x >  y'
  le  'x >= y'
  ge  'x <= y'
# in  'x in y'
# sd  'x >< y'

[ up  pas ] NB. arithmetic
  p   'x + y'
  m   'x - y'
  t   'x * y'
  q   'x / y'
  d   'x div y'
  o   'x mod y'

[ up  jmo   pas ] NB. logical operations
  a   '*.'  'x and y'
  v   '+.'  'x or  y'
  x   '~:'  'x xor y'

[ up pas ] NB. getters and setters
  // at(ix:ar of vt):ot;
  // at(ix,nv:ar of vt):ot;
)

code =: lex (0 : 0)
  pc go; bg wl('hello world') end;
  bg go end.
)
