NB. a program to find the longest cycle on a toroidal grid.
NB. http://www.reddit.com/r/dailyprogrammer/comments/2m82yz

example =: (0 : 0)
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

NB. The idea here is to assign each symbol a
NB. vector, and then to add the vector to the
NB. coordinates of the corresponding point.

'N S E W' =: H =: _1 0, 1 0, 0 1,: 0 _1
chars =: [: > [: }. <;._2      NB. input->[[char]]
links =: (H {~ '^v><' & i.)"0  NB. [[char]]->[[dy,dx]]
cells =: (#:i.)@$              NB. [[atom]]->[[ y, x]]

cycle =: adverb define
  r=.'' whilst. (-:~.) r do. r =. r , y=.u y end.
)
NB. ! the idea for the above adverb was to do something
NB.   like ^:_  (repeat until the value stops changing)
NB.   but stop on *any* previously encountered result.

NB. TODO: it doesn't quite work yet, though. :/
NB.(links step cycle cells) chars example

