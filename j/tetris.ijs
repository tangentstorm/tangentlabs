NB. Partial implementation of tetris in j by tangentstorm
NB. J is an array-oriented programming language that combines
NB. ideas from APL and combinatory logic (tacit programming)
NB. -- http://jsoftware.com/

load 'viewmat color16'


NB. --- create a blank well ---------
'w h' =: 10 20
well =: (w, h) $ 0 
NB. the coordinates appear transposed when printed,
NB. but we'll use |: to compensate

NB. --- set up the colors -------------
rgb =: 0 1 $ a: NB. set up empty list of rows
clr =: 3 : 0
  rgb =: rgb , y
)
clr 0; 'blk';   0    0    0
clr 1; 'blu';   0    0  255
clr 2; 'grn';   0  255    0
clr 3; 'cyn';   0  255  255
clr 4; 'red'; 255    0    0 
clr 5; 'mgn'; 255    0  255
clr 6; 'yel'; 255  255    0
pal =: ((#rgb),3)$ ;2{"1 rgb
show =: (pal & viewmat)


NB. --- set up the shapes -------------
S =: 2 * > 0 0 0 0; 0 1 1 0 ; 1 1 0 0; 0 0 0 0
Z =: 4 * > 1 1 0 ; 0 1 1
I =: 3 * > 0 0 0 0 ; 1 1 1 1
T =: 5 * > 1 1 1 ; 0 1 0
O =: 6 * > 0 0 0 0; 0 1 1 0; 0 1 1 0 ; 0 0 0 0

] shapes =: S ; Z; I; T; O

NB. show them off as ascii art since i learned to use 'each':
] |:('.abcdefg'{~ ])"0 each (0 _1 |. 5 5 {.]) each shapes

rr =: |:@|.
rl =: |.@|:

NB. rotate to each of the 4 headings, and embed in a larger square
frames =: ,/ @ (0 _2 _1 |: 4 5 5 {. rr^:(i.4))

rebox =: >"{

NB. join the rotated set of frames for each shape's subgrid: 
pic =: ,/|:"2 frames"2 rebox shapes

NB. just add some padding:
show _3 _2 |. (3 3 + $ pic) {. pic


NB. -- add a shape to the well -------

NB. -- draw the well -----------------
NB. show rr well
