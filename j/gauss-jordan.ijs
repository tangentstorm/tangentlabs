NB. gaus-jordan elimination
NB. =================================


   NB. some equations   
   e1 =:  1  _3   1   4  NB.   x - 3y +  z =  4
   e2 =:  2  _8   8  _2  NB.  2x - 8y + 8z = -2
   e3 =: _6   3 _15   9  NB. -6x + 3y -15z =  9

   NB. the matrix:
   M =: e1 , e2 ,: e3
 1 _3   1  4
 2 _8   8 _2
_6  3 _15  9


   NB. scale the first row by the first column 

   ] col =: 0 }"1 M
1 2 _6
   col */ e1
 1 _3  1   4
 2 _6  2   8
_6 18 _6 _24
   ] d =: 0 1 1 * col */ e1
 0  0  0   0
 2 _6  2   8
_6 18 _6 _24
   ] m =: m - d
1  _3  1   4
0  _2  6 _10
0 _15 _9  33
   ] m =: m % 1 _2 3   NB. reduce the third row.
1 _3  1   4
0  1 _3   5
0 _5 _3  11

   NB. now simplify the next column
   ] col =: 1 {"1 m
_3 _1 _5
   ] row =: 1 { m
0 _1 3 _5
   ] m - 1 0 1 * col */ row
1  _9 19 _26
0  _2  6 _10
0 _15 27 _39


   ] m =: 1 1 18 %~ m - 1 0 1 * (1 {"1 m) */ 1 { m =: 1 _2 _3 %~ m =: m - 0 1 1 * (0 {"1 m) */ 0 { m =: e1 , e2 ,: e3
1 0 _8 19
0 1 _3  5
0 0  1 _2

  ] m - 1 1 0 * (2 {"1 m) * / 2 { m
1 0 0  3
0 1 0 _1
0 0 1 _2
