Red [ "bit story" Needs: 'View ]


xx: 0 - (32x0 + 50x0)
win: view/tight/no-wait compose [
  size 960x1080

  style bit:
    base 32x32 glass loose
    data false draw [fill-pen #444 circle 16x16 15]
    on-mid-up [
      if not dragged [
        face/data: not face/data]
        face/draw/2: hex-to-rgb either face/data [#eee] [#444]
      dragged: false ]

  style var:
    text 32x32 #66c center middle
    font-name "consolas" font-size 16 font-color white

  ; --- addition scene ----------------
  origin 300x300 across space 50x25

  pad (xx) ; carry bits
  bit bit bit return

  ; input bits
  x4: var "x4" var "x2" var "x0" return
  var "x5" var "x3" var "x1" return

  pad (xx) base 280x5 black return

  pad (xx)  ; result bits
  bit bit bit bit return

  style carry: base 75x175 glass
    draw [line-width 4 pen white
      translate 10x5
      [[line 0x10 0x0 45x0 45x145 55x145 line 45x90 55x90]
       [fill-pen white triangle -5x10 5x10 0x20]]]

  origin 220x265 space 10x25
  across carry carry carry return
]

win/color: hex-to-rgb #369 ;  #113366


; -- make some "input variables"
make-vars: function[n][
  do collect [repeat i n [
    keep compose [
      (to-set-word rejoin ["x" i - 1]) var (i - 1)]]]]
