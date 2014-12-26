NB. game theory tools for j
NB. -----------------------

NB. returns 1 for each dominated row, else 0
dom =: [: +./"1 ] (*./ @: <:"1)  1]\.]

NB. return the opponent's view of the grid
opp =: -@|:

NB. remove dominated options
rmdom =: -.@dom # ]

NB. simplify by doing rmdom for both players
simp1 =: [: rmdom&:opp rmdom

NB. simplify repeatedly until no change
simp =: simp1 ^:_


NB. example game: rock paper scissors
rps =: 3 3 $ 0 _1 1,  1 0 _1,  _1 1 0

NB. example game 2 : rock, paper, scissors, flower
NB. (from mathematics of poker by bill chen & jerrod ankenman)
NB. flower loses to rock or scissors and ties with paper.
rpsf =: 4 4 $ 0 _1 1 1,  1 0 _1 0,   _1 1 0 1,   _1 0 _1 0

NB. rpsf should reduce to rock paper scissors:
assert rps -: simp rpsf


NB. example game3: rock paper scissors, with bonus for scissors
rpS =: 3 3 $ 0 _1 1,  1 0 _2,  _1 2 0


NB. solving the game:
solve =: ((1,#@]$0:) %. 1,x:)
NB. the 1=#\ forms a matrix of 1 followed by #y 0's
solve =: [: (%.~ 1=#\) 1x , ]

assert 1r3 1r3 1r3 -: solve rps
assert 1r2 1r4 1r4 -: solve rpS
