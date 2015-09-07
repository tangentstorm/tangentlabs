load'irctoys.ijs'
load'~Syn/cheq.ijs'
cc'langlet'
NB. numbers from langlets apl94 binary algebra workshop
NB. http://archive.vector.org.uk/art10004690
NB. https://docs.google.com/file/d/0B3gbSUvJhxQuRmRpam9ZWnN1UUU/edit
p=:  10153 36036 45591  4331
p=:p,34151 15707  8376 10511
p=:p,  147 19736 15590 43989
p=:p,43873 17927 48758 43736
p=:|:#:p

v=:'.X'{~]

assert p -: p (~:/ . *.)^:47523 p

Note 'cheq v p'
.XX.X......XX.XX
.........X...X..
X.X..XXX..XXX.XX
..XX.X....X...X.
.X...X.X.XXXX.XX
XX..XX...XX..XX.
X.X........XXXXX
X...XX.X.X.XX...
XX.X..X.X.XX...X
.X.XXX....XXX.XX
X..XX.X...X.X.X.
..X..XX.XX.X..XX
X..X.XXX.X.....X
.XX.X..X..XX.XX.
X.XXXX.XX.X..XX.
..XXXX.XX..XXX..
)

id =: 1 0 ,: 0 1
di =: 0 1 ,: 1 0
gh=:Gh =: 1 0 ,: 1 1
gv=:Gv =: 1 1 ,: 0 1
g=:g2=:G=: 1 1 ,: 1 0   NB. g2 means 2*2 version of g
gd=:Gd =: 0 1 ,: 1 1
z=:       0 0 ,: 0 0

ext=:13 : ',./,./> y{(z;g)' NB. extend by replacing 0->z, 1->g
r2d=: |:&.|.                NB. reflect across second diagonal

cyc=:([: >:@I. }.@:-@i.@#@] ([: *./ 2 -:/\ [\)"0 _ ])"_ L:0
m=:mm2=: 2|(+/ . *)

NB. === looking for matrices that behave like functions ==
NB. langlet asserts that all functions on bits can be replaced
NB. with matrix multiplication.

isinc =: 2 : 0
  NB. does the matrix act like 'inc' for two digit binary numbers?
  M=. n $ y
  *./(0 1 -: M u 0 0),(1 0 -: M u 0 1),(1 1 -: M u 1 0),(0 0 -: M u 1 1)
)

NB. none of the 2*2 simple matrices do.
assert -. (m isinc 2 2)"1 #:i.2^4

NB. lack of a 2*2 matrix means there is no linear mapping,
NB. because it is not a linear transformation. but apparently,
NB. it is an affine transformation, since there are eight 3*3
NB. matrices that fit the bill:
m2fn =: [: }: 2 | [ +/ .* ] , 1:  NB. matrix to function
cheq 3 3 <@$"1 #: I.(m2fn isinc 3 3)"1 ] #:i.2^9
┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐
│1 1 0│1 1 0│1 1 0│1 1 0│1 1 0│1 1 0│1 1 0│1 1 0│
│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│
│0 0 0│0 0 1│0 1 0│0 1 1│1 0 0│1 0 1│1 1 0│1 1 1│
└─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘
)

NB. does one function act like another? (wound up not using this...)
like =: 2 :('(u y) -: (v y)';':';'(x u y) -: (x v y)')
assert (2*]) like +:  i.10

NB. x u isfn v y → does (v y)&u map 0{x to 1{x?
isfn =: conjunction define
 [:
:
 *./ ([ -: (v y) u ]) S:0/ x
)

plus =: 1 : '_2 {. [: #: 4| m + #.'
NB. map u over n to produce a table
utbl =: 1 :'(< ;~ u L:0);/y'
findm =: 1 :'3 3 <@$"1 #:I.((<;~u L:0);/#:i.4) (m2fn isfn (3 3$]))"1 #:i.2^9'

sz =: 5      NB. size of the square matrix
sh =: sz,sz
sq =: sz^2
bx =: #:@:I. NB. binary index
fm =: 1 :'{. sh <@$"1 bx f. (u utbl #:i.2^sz-1) (m2fn isfn (sh$]))"1 #:i.2^sq'


Maj =: (a *. b) ~: (a *. c) ~: b *. c  NB. boolean majority
Cho =: (a *. b) ~: a < c               NB. boolean choice

NB. fractal growth operation. monad substitutes y for 1 in y
NB. (dyadic version substitutes x for 1 in y)
gro =: [: ,./^:2 [ *./ ]

NB. (his roby is rotated 90 degrees, so the numbers are different)
roby =: (16$2)#:0 864 64 320 736 544 4640 6128 5392 7452 1300 1300 2032 544 544 3640
newlife=: 'B=:(~:/\ 1|. B) ~: ~:/\ 1|."1 B=:0,0,"1 B'



cheq   ] findm
┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐
│1 0 0│1 0 0│1 0 0│1 0 0│1 0 0│1 0 0│1 0 0│1 0 0│
│0 1 0│0 1 0│0 1 0│0 1 0│0 1 0│0 1 0│0 1 0│0 1 0│
│0 0 0│0 0 1│0 1 0│0 1 1│1 0 0│1 0 1│1 1 0│1 1 1│
└─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘
)

cheq   1 plus findm
┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐
│1 1 0│1 1 0│1 1 0│1 1 0│1 1 0│1 1 0│1 1 0│1 1 0│
│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│
│0 0 0│0 0 1│0 1 0│0 1 1│1 0 0│1 0 1│1 1 0│1 1 1│
└─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘
)

cheq   2 plus findm
┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐
│1 0 1│1 0 1│1 0 1│1 0 1│1 0 1│1 0 1│1 0 1│1 0 1│
│0 1 0│0 1 0│0 1 0│0 1 0│0 1 0│0 1 0│0 1 0│0 1 0│
│0 0 0│0 0 1│0 1 0│0 1 1│1 0 0│1 0 1│1 1 0│1 1 1│
└─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘
)

cheq   3 plus findm
┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐
│1 1 1│1 1 1│1 1 1│1 1 1│1 1 1│1 1 1│1 1 1│1 1 1│
│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│0 1 1│
│0 0 0│0 0 1│0 1 0│0 1 1│1 0 0│1 0 1│1 1 0│1 1 1│
└─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘
)
cc'base'
