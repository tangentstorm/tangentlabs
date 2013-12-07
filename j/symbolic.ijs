NB. symbolic functions, expanded from an idea here:
NB. http://www.jsoftware.com/docs/help701/dictionary/samp19.htm
NB.
NB. you can use these to test whot arbitrary combinators do.

VSYM =: 1 : 0
  '(', (": m), ' ', (": y), ')' 
:
  '(', (": x) ,' ', (": m) ,' ', (": y), ')'
)

NB. declare some symbols for us to play with:
SYMS=:('x'=:'x');('y'=:'y');('m'=:'m');('n'=:'n')
SYMS=:(d=:'d'VSYM);(e=:'e'VSYM);(f=:'f'VSYM);(g=:'g'VSYM);(h=:'h'VSYM);
SYMS=:(u=:'u'VSYM);(v=:'v'VSYM)
SYMS=:''

NB. the idea here is that invoking the function creates a string:
assert         (f 0)        =   '(f 0)'
assert         (f y)        =   '(f y)'
assert       (x f y)        =   '(x f y)'

NB. now we will create two strings for each law, and test to
NB. make sure the strings equal each other.

NB. trains
NB. ---------------------------------------------------
assert         ((f g) y)    =   (y f (g y))             NB. monadic hook
assert       (x (f g) y)    =   (x f (g y))             NB. dyadic hook

assert       (  (f g h) y)  =   ((  f y) g (  h y))     NB. monadic fork
assert       (x (f g h) y)  =   ((x f y) g (x h y))     NB. dyadic fork

assert      (([: g h) y)    =   (g (  h y))             NB. monadic capped fork
assert    (x ([: g h) y)    =   (g (x h y))             NB. dyadic capped fork

assert        ((e f g h) y) =  ((e (f g h)) y)          NB. hook rule repeats when total length is even
assert        ((e f g h) y) = (y e ((f y) g (h y )))    NB. fully expanded

assert      ((d e f g h) y) = ((d e (f g h)) y)         NB. fork rule repeats when total length is even
assert      ((d e f g h) y) = ((d y) e ((f y) g (h y))) NB. fully expanded


NB. noun-verb conjunctions
NB. ---------------------------------------------------
assert       ((f & y) x)    =  (x f y)
assert       ((x & f) y)    =  (x f y)

NB. verb-verb conjunctions
NB. ---------------------------------------------------
assert        ((f &  g) y)   =  (f (g y))
assert        ((f &: g) y)   =  (f (g y))
assert        ((f @  g) y)   =  (f (g y))
assert        ((f @: g) y)   =  (f (g y))

assert        (x (f &  g) y)   =  ((g x) f (g y))
assert        (x (f &: g) y)   =  ((g x) f (g y))
assert        (x (f @  g) y)   =  (f (x g y))
assert        (x (f @: g) y)   =  (f (x g y))


NB. adverbs
NB. ---------------------------------------------------
assert       (f ~ y )       =  (y f y)

assert       (f  ~ i.3)     =  '(0 1 2 f 0 1 2)'
assert       (f  / i.3)     =  '(0 f (1 f 2))'
assert       (f ~/ i.3)     =  '((2 f 1) f 0)'

NB. gerunds
NB. ---------------------------------------------------
assert   x (f`g`h @. 0) y   =  (x f y)
assert   x (f`g`h @. 1) y   =  (x g y)
assert   x (f`g`h @. 2) y   =  (x h y)

