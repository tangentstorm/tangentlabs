NB. Program to solve a triangle from partial information.
NB. http://www.reddit.com/r/dailyprogrammer/comments/2451r5/
NB. ------------------------------------------------------------
NB.
NB.     B              | { a, b, c } = length of sides
NB.     |\             | { A, B, C } = degree of the respective
NB.     | \            |               opposing angles
NB.   a |  \ c         |
NB.     |   \          | C = 90 degrees.
NB.     |_   \         |
NB.   C |_|___\ A      |
NB.        b           |
NB.
NB. Input is a line containing a positive integer, followed
NB. by that number of lines containing facts about the triangle.
NB. Angles are given in degrees. Input will always give enough
NB. information and will describe a valid triangle.
NB.
NB. Example input:
NB. ------------------------------------------------------------
NB. 3
NB. a=3
NB. b=4
NB. C=90
NB.
NB. Expected output:
NB. ------------------------------------------------------------
NB. a=3
NB. b=4
NB. c=5
NB. A=36.87
NB. B=53.13
NB. C=90
NB. ------------------------------------------------------------
require 'trig'

NB. We will use a 6 element array to track the known
NB. information. Global array 'key' provides the
NB. labels for our array.
keys =: 'abcABC'

NB. pairs :: str -> str[2*N]
pairs =: verb define
  NB. ( ;: y ): tokenize right argument
  NB. (  }.  ): drop first token (which just contains N)
  NB. ( _4[\ ): arrange into 4 columns { space, sym, =, val }
  NB. (  }:  ): drop trailing blank row
  NB. ( 1 3 {"1 ): extract 'sym', 'val' columns
  1 3 {"1 }: _4[\ }. ;: y
)

NB. parse :: str[2*N] -> num[6]
parse =: verb define
  res =. _ _ _ _ _ 90     NB. _ (infinity) makes for a good 'blank'
  for_row. y do.
    'sym val' =. row      NB. unbox and assign cells
    idx =. keys i. sym    NB. index of symbol in key
    val =. ". val         NB. evaluate str to get num
    res =. val idx } res  NB. store in the result array
  end.
  res return.
)


NB. solve :: num[6] -> num[6]
solve =: verb define
  res =. y

  NB. helper routines
  need =. _ e. ]      NB. true if any blanks exist.
  have =. -. @ need   NB. -. means 'not', @ is composition.

  while. _ e. res do.
    'a b c A B C' =. res

    NB. 1. given either angle, we can find the other,
    NB. since the angles of a triangle sum to 180.
    NB. '*.' means and, '|' means absolute value.
    if. (need A) *. (have B) do. A =. 90 - B end.
    if. (need B) *. (have A) do. B =. 90 - A end.

    NB. 2. given any two sides, we can find the third,
    NB. since c = %: +/ *: a, b (pythagorean theorem)
    NB. '*:' is sqr, '%:' is sqrt, '+/' is sum '-/' is difference
    if. (need a) *. (have c,b) do. a =. %: -/ *: c, b end.
    if. (need b) *. (have c,a) do. b =. %: -/ *: c, a end.
    if. (need c) *. (have a,b) do. c =. %: +/ *: a, b end.

    NB. 3. if we know the sides (step 2), we can find the angles.
    NB. '%' means division. 'dfr' is degrees from radians.
    if. have a,b,c do.
      if. need A do. A =. dfr arcsin a % c end.
      if. need B do. B =. dfr arcsin b % c end.
      NB. C = 90 so we never need it.
    end.

    NB. 4. if we know the angles (from step 1),
    NB. and one side, we can calculate the other two sides.
    NB. since this loops, we only actually need to calculate 
    NB. one other side, and step 2 will fill in the other value.
    if. (have A, B, C) *. (need a,b,c) do.
      select. _ ~: a, b, c  NB. so 1 means we have it, 0 we need it
        case. 0 0 0 do. echo 'not enough information!' throw.
        case. 0 0 1 do. 'a b' =. (c * sin) rfd A, B
        case. 0 1 0 do. c =. % (sin rfd B) % b
        case. 1 0 0 do. c =. % (sin rfd A) % a

        fcase. 0 1 1 do. NB. fcase falls through to next case.
        fcase. 1 0 1 do.
        fcase. 1 1 0 do.
        fcase. 1 1 1 do. echo 'these are unreachable.' throw.
      end.
    end.
    res =. a, b, c, A, B, C
  end.
)

rounded =: <.&.(0.5 + 100 * ])  NB. round to 2 decimal places
matches =: = & rounded          NB. compare rounded numbers
check =: verb def 'try. solve parse _2[\ ;: y catch. 0 return end.'

NB.    aa.00 bb.00 cc.00 AA.00 BB.00 CC
assert  3     4     5    36.87 53.13 90   matches check 'a 3  b 4'
assert  5     8.66 10    30    60    90   matches check 'a 5  A 30'
assert  5     8.66 10    30    60    90   matches check 'a 5  B 60'
assert  5     8.66 10    30    60    90   matches check 'c 10 a 5'

NB. report :: num[6] -> IO()
NB. 0j2 ": y formats y to 2 decimal places
NB. ": ". truncates .00
report =: verb define
  for_i. i. # y do.
    echo (i{keys), '=', (": ". 0j2 ": i{y)
  end.
)

NB. main program
report solve parse pairs stdin''

