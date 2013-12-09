NB. Object class
NB. ----------------------------------------------------------
coclass <'Object'

create =: verb define
)

class =: verb define
)

destroy =: verb define
  echo '** DESTROYED!! **'
  codestroy ''
)


NB. stacks
NB. ----------------------------------------------------------
coclass <'Stack'
coinsert 'Object'

create =: verb define
  data =: y
)

push =: verb define
  data =: y ; data
)

append =: verb define
  data =: data , y
)

extend =: verb define
  data =: data , <y
)

pop =: verb define
  res =. {. data
  data =: }. data
  >res
)

tos =: verb define   NB. top of stack
  > {. data
)

result =: verb define
  data
)


NB. cocurrent <'test'
NB. stack =. '' conew 'Stack'
NB. assert result__stack = ''



NB. This builds trees of boxed objects.
NB. ---------------------------------------------------------
coclass <'Boxer'
coinsert 'Object'

create =: verb define
  state =: 0
  depth =: 0
  main  =: '' conew 'Stack'  NB. this is the main stack
  path  =: '' conew 'Stack'
  here  =: main
)

pushstate =: verb define
  depth =: depth + 1
  push__path state
  push__path here
  here  =: '' conew 'Stack'
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

append =: verb define
  append__here y
)

extend =: verb define
  extend__here y
)

result =: verb define
  result__main''
)


NB. generic parser stuff
NB. ----------------------------------------------------------
cocurrent <'script'

NB. ws y -> is character y whitespace?
ws=: 32 >: (a.i.])


NB. sx text -> tree : a simple s-expression parser
NB. ---------------------------------------------------------

bx     =: 0 conew 'Boxer'
digits =: '0123456789'

sx=: verb define
  buf =. ''         NB. buffer (current work area)

  if. (0 = # y) do. a: return. end.

  i =. 0
  while. i < # y do.
    ch   =. i { y
    drop =. 0
    emit =. 0
    hold =. 0

    echo '  state: ', (":state__bx), ' ch: ''', (":ch), '''  depth: ', (":depth__bx)

    select. state__bx

    NB. state 0 : default state (at start / between phrases)
    case. 0 do.
      if. ws ch  do.
        drop =. true NB. just skip whitespace
      elseif. ch = '(' do.
        drop =. true
        pushstate__bx 0
      elseif. ch = ')' do.
        if. depth__bx <: 0 do.
          echo 'unexpected ('
          throw.
        else.
          popstate__bx ''
          drop =. 1
        end.
      elseif. ch e. digits do.
        pushstate__bx 1
      end.

    NB. state 1 : parsing a number
    case. 1 do.
      if. -. ch e. digits do.
        popstate__bx ''
        hold =. 1
        emit =. 1
      end.

    end. NB. of select.

    NB. end of loop cleanups
    if. -. hold do. i =. i + 1 end.
    if. -. drop +. hold do.
      buf =. buf, ch     NB. consume the character.
    end.
    if. emit *. # buf do.
      append__bx <buf
      buf =. ''
    end.
  end.

  if. # buf do.
    append__bx buf
  end.

  while. depth__bx > 0 do.
    popstate__bx ''
    echo 'pop'
  end.

  result =. result__bx''
  codestroy__bx''
  result
)


assert (a:) = sx ''
NB. expecting an error here:
sx ')...'
state =: 0
sx '1 ( 2(3 4 5  ) 6) 7'
NB. ┌─┬─────────────┬─┐
NB. │1│┌─┬───────┬─┐│7│
NB. │ ││2│┌─┬─┬─┐│6││ │
NB. │ ││ ││3│4│5││ ││ │
NB. │ ││ │└─┴─┴─┘│ ││ │
NB. │ │└─┴───────┴─┘│ │
NB. └─┴─────────────┴─┘
