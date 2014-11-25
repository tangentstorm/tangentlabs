NB. unification and substitution for s-expressions in j
NB.
NB. © copyright 2014 michal j wallace < http://tangentstorm.com/ >
NB. available for use under the MIT/X11 license.
NB.
require 'boxer.ijs' NB. for sx
require 'dict.ijs'  NB. for sym/S, dict,get,put,etc


NB. symbolic substitution    (x:dict subs y:sx → sx)
NB. --------------------------------------------------------
NB. replace keys of x with corresponding values, leaving the
NB. rest of y unchanged.
subs =: [: :: (get :: ] L:_ 0)

Note (('a b c' S) dict ('x y z' S)) subs sx'(b a (n a)) ((n) a)'
┌───────────────┬─────────┐
│┌──┬──┬───────┐│┌────┬──┐│
││`y│`x│┌──┬──┐│││┌──┐│`x││
││  │  ││`n│`x│││││`n││  ││
││  │  │└──┴──┘│││└──┘│  ││
│└──┴──┴───────┘│└────┴──┘│
└───────────────┴─────────┘
)


dtype =: 3!:0 NB. datatype of y
isSym =: 65536=dtype
isBox =: 32=dtype

inRange =: (> {.) *. (< {:)
isVar   =: 0:`(inRange&('$ %'S))@.isSym
inTree  =: +./@(e.S:0)

atomic =: (1 = #) *. (-.@isBox)

nope =: 'nope'S  NB. symbol returned when unification fails
unify =: (4 : 0) NB. x uw y : 0|dict → dict if x unifies with y, else 0
  if. x -: y do. emptyd
  elseif. (isVar x) > ((isVar y) +. (x inTree y)) do. x dict y
  elseif. (isVar y) > ((isVar x) +. (y inTree x)) do. y dict x
  elseif. +./(atomic x),(atomic y),(x ~:&# y) do. nope
  elseif. (1=#x) *. (x *.&isBox y) do. , x unify & > y
  elseif. do.
    if. (hu =. x unify & {. y) -: nope do. nope   NB. unify heads
    else. tu =. x unify & (hu subs }.) y          NB. unify tails
      if. tu -: nope do. nope
      else. tu , L:_1 hu end.
    end.
  end.
)

NB. examples
assert isVar '$a'S
assert -. isVar '%a'S
assert '$a'S inTree sx'(0 (1 $a) 3)'
assert -. '$a'S inTree sx'(0 (1 2) 3)'

assert (g=.'$a'S dict 0) -: r=.('$a'S) unify 0
assert (g=.'$a'S dict 0) -: r=.(sx'$a') unify (sx'0')
assert (g=.emptyd)       -: r=.(sx'0 0') unify (sx'0 0')
assert (g=.'$a'S dict 0) -: r=.(sx'$a 0') unify (sx'0 0')
