Red [Title: "Some APL/J/K - inspired functions" ]

todo: func [what][print rejoin ["TODO: " what] halt]

iota: func ["iota: count to x-1" x [integer!] ][
  collect [repeat i x [keep (i - 1)]]]

reshape: function ["reshape" x [integer!] y [scalar! block!]] [
  either scalar? y [collect [loop x [keep y]]]
     [todo "reshape array"]]

cross: func[xs ys][r: copy []
  foreach x xs [foreach y ys [repend/only r [x y]]]]

; nest: function [x] [b: make block! [1]  b/1: x b]
nest: function [x] [repend/only copy [] x]

; n times [i] <-> iota n  (but [i] can be any expression on i)
times: make op! function [n f][
  collect [repeat i 10 [
    keep do replace/all/deep copy/deep f 'i (i - 1)]]]

map: func [f xs /local x][collect foreach x xs [keep r (f x)]]
mapx: func [fx [block!] xs /local x][
  collect [foreach xi xs [
    keep do replace/all/deep copy/deep fx 'x xi]]]

; this only gives you monadic versions
apl-glyphs: does [ ρ: :rs  ⍳: :io ]

~ws: charset reduce [space tab cr lf]
~digit: charset "0123456789"
~number: [opt "-" some ~digit]

; k insert operator
k-ins: func['dy xs][
  collect [keep first xs
    foreach x next xs [keep dy keep x]]]

kp-op: charset "+!,"
kp-noun?: [~number ]
kp-noun: [copy num kp-noun? keep (to-integer num)]
kp-mo-v:
  [ "!" keep ('iota)
  | "+" keep ('flip)
  | "," keep ('nest)]
kp-dy-v:
  [ "!" keep ('modx)
  | "+" keep ('+)
  | "," keep ('join) ]
kp-monad:
  [ [ahead [kp-op "/"]] keep ('k-ins) kp-dy-v skip
  | kp-mo-v
  ]
kp-expr: [any ~ws collect [
  any [kp-monad
      | ahead [kp-noun? kp-op]
        kp-noun
        kp-dy-v ]
  kp-noun]]

kp: function[s][parse s kp-expr]
k: function[s][do parse s kp-expr]

'ok
