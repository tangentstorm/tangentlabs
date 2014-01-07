NB. this file exposes two new verbs: X and Y , which
NB. return the left and right arguments of an entire
NB. train.

Xv =: _. [ Yv =: _.        NB. global variables to hold the arguments.
Y =: 3 : (;:' Yv : Yv ')   NB. Y simply returns the current value of Yv
X =: 3 : (;:' [: : Xv ')   NB. X returns Xv, but fails in monadic contexts.

NB. the xy adverb modifies a verb so that it stores its arguments
NB. in Xv and Yv, hiding the previous values on the stack and 
NB. restoring them afterward.
xy =: 1 : 0
  Yv =: y  [ oY =. Yv
  try. r  =. u y  catch. r =. _. end.
  Yv =: oY
  r return.
:
  Yv =: y  [  Xv =: x  [ oY =. Yv [ oX =. Xv
  try. r  =. x u y  catch. r =. _. end.
  Yv =: oY [  Xv =: oX
  r return.
)

NB. examples:
NB. ----------------------------------

assert 25 =              ([: *: Y)xy 5
assert 25 = 2 (Y + 0:)xy ([: *: Y)xy 5


NB. difference compared to [ and ] :

ind =: '_.' -: ":  NB. true if result is indeterminate

assert   3  =   ([ Y ])xy 3
assert   5  =   ([ Y ])xy 5
assert   2  = 2 ([ X ])xy 3
assert  ind     ([ X ])xy 5     NB. no x argument to the train, so we get _.


assert 10 = (*: ] +:)   5       NB. +:5 -> 10
assert 25 = (*: [ +:)   5       NB. *:5 -> 10
assert  5 = (*: Y +:)xy 5       NB. results of *:5 and +:5 are ignored
assert ind  (*: X +:)xy 5       NB. no X argument supplied


assert 0 = 0 (*: ] +:)xy 1      NB. 1+:0 -> 0 (logical nor)
assert 1 = 0 (*: Y +:)xy 1      NB. 1 is the right argument to the train

assert 1 = 0 (*: [ +: )xy 1     NB. 1*:0 -> 1 (logical nand)
assert 0 = 0 (*: X +: )xy 0     NB. 0 is the left argument to the train
assert ind 1 (*: X +: )xy 2     NB. 1*:2 and 1+:2 both throw domain errors


NB. stack handling features:

f =: (Y + (2 ^ Y) + 3 ^ Y) xy
g =: (X * [: f [: i. Y) xy
h =: (+: g +:)

NB. above, h calls g and g calls f.
NB. the calls to X and Y do the right thing because
NB. xy takes care of managing the stack.

assert  8 24 60 152 = 4 g 4
assert  8 24 60 152 = h 2

assert 2 6 15 38 = f 0 1 2 3
assert 2 6 15 38 = 1 g 4
assert ind           g 4
