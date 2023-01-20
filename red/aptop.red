Red [ Title: "tiny language inpsired by Eric Hehner's {A Practical Theory of Programming}"]

;-- helper functions (might already exist in red?)
map: func [f xs /local r x][r: make block! [] foreach x xs [append r (f x)]]
nest: function [x] [b: make block! [1]  b/1: x b] ; !! is there a better way to take [x] -> [[x]] ??

rest: :next
warn: function [msg] [print rejoin ["WARNING: " msg]]
todo: func [what][print rejoin ["TODO: " what] halt]
assert: function ["halt with msg unless cond is true" cond [block!] msg [string!]]
  [unless (do cond) [print rejoin ["assertion failed: [" form (rejoin cond) "] " mold msg] halt]]


;-- interpreter
new-ctx: function ["create a new (empty) context"] [make map! []]
exec: function ["execute P in new context" P [block!]] [exin new-ctx P]
exin: function ["execute P in context ctx" ctx [map!] P [block!]] [
  if tail? P [return ctx]
  assert [block? node: first P] rejoin ["Program P should be a list of blocks! got:" P]
  assert [lit-word! = type? tag: node/1] rejoin ["tag should be lit-word ('ok), got: " node/1]
  switch/default tag [
    'ok    [ctx/'res: none]       ; ['ok]
    'val   [ctx/'res: do node/2]  ; ['val 1234]
    'block [exin ctx rest node]   ; ['block ['ok] ['ok]]
    'if    [exin ctx nest either evin ctx nest node/2 [node/3] [node/4]]
    'while [todo "WHILE!"]        ; ['while cond-expr do-prog]
    'emit  [print form rest node] ; ['emit "just for debugging"]
  ][print rejoin ["invalid tag: " first this] halt]
  exin ctx rest P]

evin: function ["eval E in ctx (preserving ctx/'res)" ctx [map!] E [block!]] [
  old: ctx/'res
  tmp: exin ctx to-block E
  res: tmp/'res
  ctx/'res: old
  res]

;-- test suite
after: func [P] [ctx: exec P]
expect: func [res msg] [assert [ctx/'res = res] msg]

after [  ] expect  none "empty program shouldn't have a result"
after [['ok]] expect  none "ok shouldn't have a result"
after [['block ['ok]]] expect  none "allow nested blocks"
after [['val 5]] expect 5 "'val should set return value"
after [['if ['val true] ['val 't] ['val 'e]]] expect 't "if true -> then"
after [['if ['val false] ['val 't] ['val 'e]]] expect 'e "if false -> else"
"ok!"
