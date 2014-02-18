NB. Object class
NB. ----------------------------------------------------------
coclass 'Object'

create  =: verb def ''
class   =: verb def ''
destroy =: verb define
  NB. echo '** DESTROYED!! **'
  codestroy ''
)

NB. stacks of like objects
NB. ----------------------------------------------------------
coclass  'Stack'
coinsert 'Object'

create =: monad def ('data =: y')
pop    =: monad define
 res  =. {. data
 data =: }. data
 res
)
push   =: monad def ('data =: y , data')
append =: monad def ('data =: data , y')
extend =: append
tos    =: monad def ('> {. data')    NB. top of stack
result =: monad def ('data')


NB. stacks of boxed objects (mixed types)
NB. ----------------------------------------------------------
coclass  'BoxStack'
coinsert 'Stack'

NB. overrides:
extend =: [: extend_Stack_ f. <
push   =: [:   push_Stack_ f. <
tos    =: [: > tos_Stack_  f.
pop    =: [: > pop_Stack_  f.

NB. This builds trees of boxed objects.
NB. ---------------------------------------------------------
coclass  'Boxer'
coinsert 'Object'

create =: verb define
  state =: 0
  depth =: 0
  main  =: '' conew 'BoxStack'
  path  =: '' conew 'BoxStack'
  here  =: main
)

pushstate =: verb define
  depth =: depth + 1
  push__path state
  push__path here
  here  =: '' conew 'BoxStack'
  state =: y
)

popstate =: verb define
  tmp   =. result__here''
  there =. here
  here  =: pop__path''
  if. # tmp do. extend__here tmp end.
  state =: pop__path ''
  depth =: depth - 1
  destroy__there''
)

append =: monad def 'append__here y'
extend =: monad def 'extend__here y'
result =: monad def 'result__main _'

NB. generic parser stuff
NB. ----------------------------------------------------------
cocurrent 'base'

NB. ws y -> is character y whitespace?
ws=: 32 >: (a.i.])


NB. sx text -> tree : a simple s-expression parser
NB. ---------------------------------------------------------

digits =: '0123456789'

sx =: verb define
  if. (0 = # y) do. a: return. end.
  i =. 0 [  (bx =. a: conew 'Boxer') [ buf =. ''  NB. buffer (current work area)

  while. i < # y do.
    ch   =. i { y [ 'drop emit hold' =. 0 0 0
    echo'  state: ',(":state__bx),' ch: ''',(":ch),'''  depth: ',(":depth__bx)
    select. state__bx
    case. 0 do.  NB. default state (at start / between phrases)
      if. ws ch  do. drop =. 1 NB. just skip whitespace
      elseif. ch = '(' do. drop =. 1 [ pushstate__bx 0
      elseif. ch = ')' do.
        if. depth__bx <: 0 do. echo 'unexpected (' throw.
        else. popstate__bx'' [ drop =. 1 end.
      elseif. ch e. digits do. pushstate__bx 1 end.
    case. 1 do.
      if. -. ch e. digits do. popstate__bx '' [ 'hold emit' =. 1 1 end.
    end. NB. of select.

    NB. end of loop cleanups
    if. -. hold do. i =. i + 1 end.
    if. -. drop +. hold do. buf =. buf, ch end.  NB. consume the character.
    if. emit *. # buf do. (append__bx <buf) [ buf =. '' end.
  end.

  if. # buf do. append__bx buf end.
  while. depth__bx > 0 do. popstate__bx '' end.
  (result__bx'') [ codestroy__bx''
)

assert a: = sx ''
echo '-- expecting an error here:'
sx ')...'
echo '-- ok, now let''s parse an s-expression:'
state =: 0
echo sx '1 ( 2(3 4 5  ) 6) 7'
NB. ┌─┬─────────────┬─┐
NB. │1│┌─┬───────┬─┐│7│
NB. │ ││2│┌─┬─┬─┐│6││ │
NB. │ ││ ││3│4│5││ ││ │
NB. │ ││ │└─┴─┴─┘│ ││ │
NB. │ │└─┴───────┴─┘│ │
NB. └─┴─────────────┴─┘
