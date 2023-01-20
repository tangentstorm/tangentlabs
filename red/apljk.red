Red [Title: "Some APL/J/K - inspired functions" ]

todo: function [what] [print append [todo:]  what halt]

io: func ["iota: count to x-1" x [integer!] ][
  res: make block! []
  repeat i x [append res (i - 1)]]

rs: func [x [integer!] y [scalar! block!]] [
  res: make block! []
  either scalar? y [loop x [append res y]] [todo "reshape array"]]

ρ: :rs  ⍳: :io