NB. based on dyalog APL video from
NB. https://www.youtube.com/watch?v=a9xAKttWgP4
i.9
3 3 $ i.9
] r =: (3 3 $ i.9) e. 1 2 3 4 7
5 7 {. r NB. enlarge
2 |."1 [ 5 7 {. r NB. center vertically
] R =: _1 |. _2 |."1 [ 5 7 {. r NB. and horizontally 
R , R ,: R  NB. three copies
  
NB. display routine (boxes 2d arrays and replaces 0 with _)
disp =: [: <"2 (+ (_ * 0 = ]))
  
disp  R, R ,: R  NB. boxed at the 2nd rank(dimension)
disp 1 0 _1 |."0 2 [ R, R,: R  NB. rotated
disp 1 0 _1 |."0 2 / ,: R  NB. using only one copy
disp 1 0 _1 |."0 1 / 1 0 _1 |."0 2 /  ,.R
disp +/+/ 1 0 _1 |."0 1 / 1 0 _1 |."0 2 /  ,.R
disp 3 4 =/ +/+/ 1 0 _1 |."0 1 / 1 0 _1 |."0 2 / ,.R  NB. find values that are 3 or 4
NB. now we want count = 3 (birth) or count=4 including original (keepalive)
disp (1,:R) *. 3 4 ="0/ +/+/ 1 0 _1 |."0 1 / 1 0 _1 |."0 2 /  ,.R
disp +./ (1,:R) *. 3 4 ="0/ +/+/ 1 0 _1 |."0 1 / 1 0 _1 |."0 2 /  ,.R NB. or together.

life =: 3 : '+./ (1,: y) *. 3 4 ="0/ +/+/ 1 0 _1 |."0 1 / 1 0 _1 |."0 2 / ,. y'

disp life R

NB. another (messier) tranlation that uses boxes throughout 
life =: 3 : '+./>((3=]);(y*.4=])) +/+/> 1 0 _1 |."_&.>/ [ 1 0 _1 |."_1&.> <  y '
_ * -. ( life^:(<8) ) (i. 15 20)  e. 111 112 113 93 72

  1
