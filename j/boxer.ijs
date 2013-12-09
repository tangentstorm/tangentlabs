

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
  echo 'new stack created'
)

destroy =: verb define
  codestroy ''
)

push =: verb define
  data =: y , data
)

pop =: verb define
  result =. {. data
  data =: }. data
  result
)

tobox =: verb define
  < data
)


NB. This builds trees of boxed objects.
NB. ---------------------------------------------------------
coclass <'Boxer'

create =: verb define
  state =: 0
  depth =: 0
  main  =: '' conew 'Stack'  NB. this is the main stack
  path  =: '' conew 'Stack'
  here  =: '' conew 'Stack'
)

pushstate =: verb define
  depth =: depth + 1
  push__path state
  state =: y
)

popstate =: verb define
  state =: pop__path ''
  depth =: depth - 1 
)

append =: verb define
  0
)

result =: verb define
  tobox__main 0
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

true  =: 1
false =: 0

sx=: verb define
  buf =. ''         NB. buffer (current work area)

  if. (0 = # y) do. a: return. end.

  i =. 0
  while. i < # y do.
    ch   =. i { y
    skip =. false
    emit =. false

    echo 'ch: ', ch, '  state: ', ": state__bx

    select. state__bx
    
    NB. state _ : error handler
    case. _ do.
      a: return.

    NB. state 0 : default state (at start / between phrases)
    case. 0 do.
      if. ws ch  do.
        skip =. true NB. just skip whitespace        
      elseif. ch = '(' do. 
        pushstate__bx 0
      elseif. ch = ')' do.
        if. depth__bx <: 0 do. 
          echo 'unexpected ('
          throw.
        else. 
          popstate__bx ''
        end.
      elseif. ch e. digits do.
        pushstate__bx 1
      end.

    NB. state 1 : consume all digits in a number
    case. 1 do.
      if. -. ch e. digits do.
        popstate__bx ''
        emit =. true
      end.
      
    end. NB. of select.
    
    NB. end of loop cleanups
    i =. i + 1
    if. -. skip do.
      buf =. buf, ch     NB. consume the character.
    end.
    if. emit do.
      buf =. ''
    end.  
  end.
  result__bx''
)


assert (a:) = sx ''
NB. expecting an error here:
sx ')...'
state =: 0
sx '1  2 (3 4 5) 6'
