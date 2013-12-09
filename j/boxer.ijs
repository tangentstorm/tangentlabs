

NB. Object class
NB. ----------------------------------------------------------
coclass <'Object'

create =: verb define
)

class =:
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


NB. This builds trees of boxed objects.
NB. ---------------------------------------------------------
coclass <'Boxer'

create =: verb define
  state =: 0
  depth =: 0
  main  =: 0 conew 'Stack'  NB. this is the main stack
  path  =: 0 conew 'Stack'
  here  =: 0 conew 'Stack'
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
  
)


NB. generic parser stuff
NB. ----------------------------------------------------------
cocurrent <'script'

NB. ws y -> is character y whitespace?
ws=: 32 >: (a.i.])


NB. sx text -> tree : a simple s-expression parser
NB. ---------------------------------------------------------

bx =: 0 conew 'Boxer'

sx=: verb define
  buf =. $0         NB. buffer (current work area)
  res =. $0         NB. result (root of the parse tree)

  if. (0 = # y) do. a: return. end.

  for_ch. y do.

    echo 'ch: ', ch, '  state: ', ": state__bx

    select. state__bx
    
    NB. state _ : error handler
    case. _ do.
      a: return.

    NB. state 0 : default state (at start / between phrases)
    case. 0 do.
      if.     ws ch    do. NB. nothing. just skip whitespace        
      elseif. ch = '(' do. pushstate__bx 0
      elseif. ch = ')' do.
        if. depth__bx <: 0 do.  echo 'unexpected (' throw.
        else. popstate__bx '' end.
      end.

    NB. state 1 : reading a word
    case. 1 do.
      if.       ch = ')'   do.  popstate__''
      end.
    end.

    NB. if still here, consume the character.
    buf =. buf, ch
  end.
  <res
)



assert (a:) = sx ''
NB. expecting an error here:
sx ')...'
state =: 0
sx '1  2 (3 4 5) 6'
state
