Red [ "start on generative graphics" ]

TRI: [[triangle 100x100 110x84 120x100]]
v: view/tight/no-wait [ base 640x480 #133366 ]
t: collect  [repeat x 5 [
  keep compose [translate (as-pair x * 25 0) (TRI)]]]

v/pane/1/draw: compose [scale 0.9 0.9 line-width 1 fill-pen white (t)]
