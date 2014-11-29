NB. cheq y : checks that the result of y is equal to the following noun
cocurrent'cheq'

NB. unicode box chars. (j magically translates these to unicode for display)
uboxch=: [: (9!:7) (a.{~16 17 18 19 20 21 22 23 24 25 26)"_

aboxch =:   16   26   17   18   25   22   23   24   19   20   21
NB.          ┌    ─    ┬    ┐    │    └    ┴    ┘    ├    ┼    ┤
uboxch =: 9484 9472 9516 9488 9474 9492 9524 9496 9500 9532 9508

forcerank =: ,@] $~ -@[ {.!.1 [: $ ]

NB. function to apply the map to ascii string y, leaving other chars unchanged
a2ubox=: ((uboxch {~ aboxch i. ]) ::] ])&.(3 u:])"0
lines =: [: (<;._2) 7 u: ]

cheq =: 3 : 0
  expect=: > lines 0 : 0
  actual=: a2ubox 2 forcerank ": y
  if. actual -: expect do.
  else.
    echo ''
    echo 'actual=:'
    echo actual
    echo 'expect=:'
    echo expect
    'actual -: expect' assert actual -: expect
    0$0
  end.
)
cheq_z_=:cheq_cheq_

NB. examples:

cheq (];$) 2 forcerank i. 3 3
┌─────┬───┐
│0 1 2│3 3│
│3 4 5│   │
│6 7 8│   │
└─────┴───┘
)

cheq (];$) 2 forcerank i. 3
┌─────┬───┐
│0 1 2│1 3│
└─────┴───┘
)

cheq i.5
0 1 2 3 4
)

cheq (5!:4)<'lines'
  ┌─ [:
  │      ┌─ <
  ├─ ;. ─┴─ _2
──┤
  │      ┌─ 7
  └──────┼─ u:
         └─ ]
)
