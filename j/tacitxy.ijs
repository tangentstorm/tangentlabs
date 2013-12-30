NB. this file exposes two new verbs: X and Y , which
NB. return the left and right arguments of an entire
NB. train.

NB. difference compared to [ and ] :
NB.   (*: [ +: ) 5    -> 10
NB.   (*: Y +: )xy 5  -> 5
NB.   (*: ] +: ) 5    -> 
NB.   (*: X +: )xy 5  -> _.  (no x given to the train)
NB. 1 (*: X +: )xy 5  -> 1  XXX broken :(

NB. 2 ([  X  ])xy 3   -> 2  (as expected)
NB. 2 (*: X +:)xy 3   -> _. (why?)



X =: 3 : ('Xv'; ':'; 'Xv')
Y =: 3 : ('Yv'; ':'; 'Yv')
Xv =: _. [ Yv =: _. NB. the values

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
f =: (Y + (2 ^ Y) + 3 ^ Y) xy
g =: (X * [: f [: i. Y) xy
h =: (+: g +:)

) 2 (Y+0:)xy ([: *: Y)xy 5
