NB. a program to find the longest cycle on a toroidal grid.
NB. http://www.reddit.com/r/dailyprogrammer/comments/2m82yz

NB. 'cheq' is short for 'check equality' and is from:
NB.
NB.     https://github.com/tangentstorm/syndir
NB.
NB. The 'import' verb comes from `startup.ijs` in that same repo,
NB. and tries to treat files and locales as modules rather than
NB. following the j convention of cramming every new word into 'z'.
NB.
NB. If you prefer not to mess with that, you can change this
NB. line to one of the following alternatives:
NB.
NB. corequire 'cheq' [ load 'cheq.ijs' NB. for cheq.ijs
cheq =: verb def '(0 : 0) [ y'      NB. to not need cheq.ijs at all.


NB. The idea here is to assign each symbol a
NB. vector, and then to add the vector to the
NB. coordinates of the corresponding point.

NB. 'LOOP' is a sample input demonstrating a clockwise loop.
LOOP=: noun define
2 2
>v
^<
)

NB. 'WRAP' is the same loop, but shifted diagonally so it wraps.
WRAP =: noun define
2 2
<^
v>
)

NB. 'chars' strips out the line feeds and the header line.
chars =: [: > [: }. <;._2      NB. input->[[char]]
cheq chars LOOP
>v
^<
)

NB. 'cells' gives the array index for each atom.
cells =: (#:i.)@$              NB. [[atom]]->[[ y, x]]
cheq <"2 cells chars LOOP
┌───┬───┐
│0 0│1 0│
│0 1│1 1│
└───┴───┘
)


NB. 'dydx' converts the ^v>< symbols into direction vectors.
NB. (I added ' ' -> X = 0 0 to mean no movement.)
'N S E W X' =: DIR =: _1 0, 1 0, 0 1, 0 _1 ,: 0 0
dydx =: (DIR {~ '^v>< ' & i.)"0  NB. [[char]]->[[dy,dx]]
cheq <"2 dydx chars LOOP
┌───┬─────┐
│0 1│_1  0│
│1 0│ 0 _1│
└───┴─────┘
)

NB. 'cycle' collects values from an iterated process until
NB. it encounters a repeat value, and then returns all the
NB. values it saw.
cycle =: adverb define
  NB. like (^:a:) but stops on *any* already-seen value.
  r=.,:y whilst. (-:~.) r do. r =. r , y=.  u y end. r
:
  r=.,:y whilst. (-:~.) r do. r =. r , y=.x u y end. r
)

NB. example: incrementing modulo 5
cheq (5 | 1 + ]) cycle 2
2 3 4 0 1 2
)

NB. here's a 2d case. note that the initial value isn't
NB. part of the cycle.
cheq |: (2 5 | 1 2 + ]) cycle 2 2
2 1 0 1 0 1 0 1 0 1 0 1
2 4 1 3 0 2 4 1 3 0 2 4
)

NB. 'next' takes a table of '^V><' chars and constructs
NB. a new table, which maps cell coordinates to the new
NB. coordinate after following the vector and wrapping.
next =: ($ |"1 cells + dydx)
cheq <"2 next chars LOOP
┌───┬───┐
│0 1│0 0│
│1 1│1 0│
└───┴───┘
)
assert (next chars WRAP) -: (next chars LOOP)

NB. 'paths' finds the complete path for each cell, up
NB. to the point where it starts to cycle. It *has* to
NB. cycle at some point, because the space is finite.
NB. The paths are boxed since they may be different lengths.
paths =: next <@({::~ cycle)"_ 1 cells
cheq paths chars LOOP
┌───┬───┐
│0 0│0 1│
│0 1│1 1│
│1 1│1 0│
│1 0│0 0│
│0 0│0 1│
├───┼───┤
│1 0│1 1│
│0 0│1 0│
│0 1│0 0│
│1 1│0 1│
│1 0│1 1│
└───┴───┘
)

NB. 'iscyc': is easy: cycles start and end with the same coordinates.
iscyc =: {. -: {:  NB. head matches tail
cheq iscyc each ;:'abc abca aa ab aaa'
┌─┬─┬─┬─┬─┐
│0│1│1│0│1│
└─┴─┴─┴─┴─┘
)
cheq iscyc every paths chars LOOP
1 1
1 1
)

NB. 'cyclen' is the cycle length, or 0 if not a cycle.
NB. The cycle length is just 1 less than the length of the path.
cyclen =: (iscyc * <:@#)
cheq cyclen every paths chars LOOP
4 4
4 4
)

NB. Here is another example input that shows some more
NB. complex cycles. Note that each ' ' cell is a loop of length 1.
WIDE =: noun define
3 4
>>>>>v   ><  v<<
  ^  v<<<<   v ^
  ^<<<   ^   >>^
)
cheq cyclen every paths chars WIDE
0 0 10 10 10 10 1 1 1 2 2 1 1 8 8 8
1 1 10  1  1 10 0 0 0 0 1 1 1 8 1 8
1 1 10 10 10 10 1 1 1 0 1 1 1 8 8 8
)

NB. 'ismax' returns a bitmask indicating copies of the max item.
ismax =: (= >./@,)
cheq ismax 1 5 3 4 5 2 _5
0 1 0 0 1 0 0
)

NB. 'x m mask y' replaces items of x with m where y=1
mask =: adverb define
:
  x (m"0`[@.]"0) y
)

NB. 'maxcyc' puts all af this together to show the longest path.
maxcyc =: ' ' mask  [: ismax [: cyclen&> paths
cheq < maxcyc chars WIDE
┌────────────────┐
│  >>>v          │
│  ^  v          │
│  ^<<<          │
└────────────────┘
)

NB. Finally, the example input:
EXAMPLE =: (0 : 0)
45 20
^^v>>v^>>v<<<v>v<>>>>>>>>^vvv^^vvvv<v^^><^^v>
>><<>vv<><<<^><^<^v^^<vv>>^v<v^vv^^v<><^>><v<
vv<^v<v<v<vvv>v<v<vv<^<v<<<<<<<<^<><>^><^v>>>
<v<v^^<v<>v<>v<v<^v^>^<^<<v>^v><^v^>>^^^<><^v
^>>>^v^v^<>>vvv>v^^<^<<<><>v>>^v<^^<>v>>v<v>^
^^^<<^<^>>^v>>>>><>>^v<^^^<^^v^v<^<v^><<^<<<>
v<>v^vv^v<><^>v^vv>^^v^<>v^^^>^>vv<^<<v^<<>^v
<<<<<^<vv<^><>^^>>>^^^^<^<^v^><^v^v>^vvv>^v^^
<<v^<v<<^^v<>v>v^<<<<<>^^v<v^>>>v^><v^v<v^^^<
^^>>^<vv<vv<>v^<^<^^><><^vvvv<<v<^<<^>^>vv^<v
^^v^>>^>^<vv^^<>>^^v>v>>v>>v^vv<vv^>><>>v<<>>
^v<^v<v>^^<>>^>^>^^v>v<<<<<>><><^v<^^v><v>^<<
v>v<><^v<<^^<^>v>^><^><v^><v^^^>><^^<^vv^^^>^
v><>^><vv^v^^>><>^<^v<^><v>^v^<^<>>^<^vv<v>^v
><^<v>>v>^<<^>^<^^>v^^v<>>v><<>v<<^><<>^>^v<v
>vv>^>^v><^^<v^>^>v<^v><>vv>v<^><<<<v^<^vv<>v
<><<^^>>^<>vv><^^<vv<<^v^v^<^^^^vv<<>^<vvv^vv
>v<<v^><v<^^><^v^<<<>^<<vvvv^^^v<<v>vv>^>>^<>
^^^^<^<>^^vvv>v^<<>><^<<v>^<<v>>><>>><<^^>vv>
<^<^<>vvv^v><<<vvv<>>>>^<<<^vvv>^<<<^vv>v^><^
)
cheq < maxcyc chars EXAMPLE
┌─────────────────────────────────────────────┐
│                    >>>>>^                   │
│                    ^<                       │
│                     ^                       │
│                    >^                       │
│                    ^                        │
│                   >^                        │
│                   ^                         │
│                >>>^                         │
│                ^                            │
│                ^<                           │
│                 ^                           │
│                 ^                           │
│                 ^                           │
│                >^                           │
│                ^                            │
│                ^                            │
│                ^  v<<                       │
│                ^<<< ^                       │
│                     ^<<                     │
│                       ^<<                   │
└─────────────────────────────────────────────┘
)

NB. The actual goal was just to find the max cycle length:
maxCycLen=: [: >./@, [: cyclen every paths
cheq maxCycLen chars EXAMPLE
44
)
