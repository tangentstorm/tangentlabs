(0 : 0) NB. syntax experiments in J
--------------------------------------------------
Adverbs and conjunctions to simulate traditional
flow control keywords in J.

(current "best" versions are at the bottom)
--------------------------------------------------
Copyright © 2014 Michal J Wallace
License : http://opensource.org/licenses/MIT
)

a_z_ =: assert  NB. names in z accessible anywhere



0#[0 : 0]#( cocurrent 'ifThen0' )################0

If / Then / Else  v.0
==================================================

  usage:        if u then (v else w)
  means:    ] (v :. w)^:([: -. [: +: [: -. u)"0

In this version, both 'then' and 'else' are
conjunctions, while 'if' is simply the ']' verb.

The resulting train is a monadic hook operating on
rank 0. It can be used in a dyadic context, but
will simply ignore its left argument.

The '(v else w)' part requires parentheses, but
the phrase as a whole does not.

The core idea here is:

     _1 1 = ([: -. [: +: [: -. ]) 0 1

The word 'then' creates a new verb that applies
this transformation to (u y), and uses the result
to select either the verb to the right of 'then',
or its obverse. The word 'else' is simply an alias
for ':.', which creates a verb that acts like 'v'
but with obverse 'w'.

(Based on an idea by Sam Falvo.)
)

_ [' code ']_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

if =: ]
then =: 2 : 'v^:([: -. [: +: [: -. u)"0'
else =: :.

_ [' test ']_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

a   4 1 0 2 4  -:   if (<0:) then (*: else +:)  i:2
a   4 1 0 2 4  -:  (if (<0:) then (*: else +:)) i:2
a  (if ] then (| else -.)) 1 1 0 0 1 0 1 0
a   if ] then (| else -.)  1 1 0 0 1 0 1 0



0#[0 : 0]#( cocurrent 'ifThen1' )################0

Python-style conditional expressions:
==================================================

  usage:     m if v else n
  means:

With this syntax, 'if' and 'else' appear between
arguments, so they must both be conjunctions. The
result is a monadic verb.

This time, 'if' produces a new verb that returns
either 'm' or '_.' ("indeterminate"), and 'else'
checks for '_.' and replaces it with 'n'.

)

_ [' code ']_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

NB. typeOf based on type_z_. returns symbol out of:
NB. invalid/undefined/noun/adv/conj/verb/unknown
boxopen =: <^:(L. = 0:) NB. boxopen_z_
typeOf =: ({&(s:' i un n a c v ?')@(2&+)@(4!:0)&boxopen)
V =: typeOf 'typeOf'
N =: typeOf 'V'

if =: 2 : 0
select. V=(typeOf 'u'),(typeOf'v')
  case. 0 0 do. if.   n do.   m else. _. end.
  case. 0 1 do. if. v y do.   m else. _. end.
  case. 1 0 do. if.   n do. u y else. _. end.
  case. 1 1 do. if. v y do. u y else. _. end.
end.
:
  [:
)

isNaN =: 128!:5 NB. checks for _.

else =: 2 : 0
NB. left arg would normally be the result of
NB. 'if', but we might as well cover all cases,
NB. and let you use 'else' by itself too.
select. V=(typeOf 'u'),(typeOf'v')
  case. 0 0 do. if. isNaN r=.  m do.   n else. r end.
  case. 0 1 do. if. isNaN r=.  m do. v y else. r end.
  case. 1 0 do. if. isNaN r=.u y do.   n else. r end.
  case. 1 1 do. if. isNaN r=.u y do. v y else. r end.
end.
:
[:
)

_ [' test ']_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

NB. no matter what arguments go into 'if'...
(nn0 =: (0  if 0))[(nv0 =: (1  if 0:))
(vn0 =: (2: if 0))[(vv0 =: (3: if 0:))
(nn1 =: (4  if 1))[(nv1 =: (5  if 1:))
(vn1 =: (6: if 1))[(vv1 =: (7: if 1:))

NB. ... the thing that comes out is a verb:
a V=typeOf 'nn0';'nv0';'vn0';'vv0';'nn1';'nv1';'vn1';'vv1'

NB. The thing that comes out of the verb is:
NB. ... indeterminate when the (v y)/m condition is 0
a      '_. _. _. _.' = ": (nn0, nv0, vn0, nn0)''
NB. ... equal to (u y) or n otherwise.
a      4 5 6 7 = (nn1, nv1, vn1, vv1)''


a '<<<<<O>>>>>' = ('O' if (=0:) else ('<' if (<0:) else '>'))"0 i:5


NB. --- current 'best' versions -----------------
0#[0 : 0]#( cocurrent 'syntax' )################0

python-style conditionals, simplified
==================================================

  usage:     m if v else n

This version was demonstrated by Raul Miller on
the j programmers mailing list.

It seems that using "_ accounts for both verb
and noun cases.
)

if  =: 2 : ' u"_`(v"_) '
else=: 2 : ' v"_`(0{m)@.((1{m)`:6) '


if_z_ =: if_syntax_
else_z_ =: else_syntax_
