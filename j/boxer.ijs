NB. boxer: class and s-expression parser to create nested objects

load 'cheq.ijs' NB. for unit tests at the end

NB. stacks of like objects
NB. ----------------------------------------------------------
coclass  'Stack'

create =: monad def ('data =: y')
pop    =: monad def ('>[/''res data'' =: split data')
push   =: monad def ('data =: y , data')
append =: monad def ('data =: data , y')
extend =: append
top    =: monad def ('> {. data')    NB. top of stack
result =: monad def ('data')
destroy=: codestroy

NB. stacks of boxed objects (mixed types)
NB. ----------------------------------------------------------
coclass  'BoxStack'
coinsert 'Stack'

NB. overrides:
extend =: [: extend_Stack_ f. <
push   =: [:   push_Stack_ f. <
tos    =: [: > top_Stack_  f.
pop    =: [: > pop_Stack_  f.


NB. Boxers build trees of boxed objects.
NB. ---------------------------------------------------------
coclass  'Boxer'

create =: monad define
  state =: 0
  depth =: 0
  main  =: '' conew 'BoxStack'
  path  =: '' conew 'BoxStack'
  here  =: main
)

pushstate =: monad define
  depth =: depth + 1
  push__path state
  push__path here
  here  =: '' conew 'BoxStack'
  state =: y
)

popstate =: monad define
  tmp   =. result__here''
  there =. here
  here  =: pop__path''
  if. # tmp do. extend__here tmp else. extend__here a: end.
  state =: pop__path ''
  depth =: depth - 1
  destroy__there''
)

append =: monad def 'append__here y'
extend =: monad def 'extend__here y'
result =: monad def 'result__main _'
destroy=: verb define
  coerase here,path
  codestroy''
)


NB. helpers for s-expression parser
NB. ----------------------------------------------------------
cocurrent'sx'

ord     =: a. i. ]
chr     =: a. {~ ]
between =: ( ([ >: {.@]) *. ([ <: {:@]) )
span    =: ([ + [: i. >:@-~)/
chspan  =: span&.ord L:0
groups  =: chspan cut ' ''  (  )  09  AZ  `  az'

NB. escape special characters in rx sets
altesc  =: ((];'\',])"0 '^[\]-')&stringreplace

NB. m subst n y : replace leaves matching m with n in tree y
subst =: 2 :'(]`(n"_))@.(-:m"_) L:0'

NB. verb to classify x according to groups y:
class =: (1 i.~e.S:0)"0 _


NB. sx text -> tree : a simple s-expression parser
NB. ---------------------------------------------------------
spaces =: a.{~ i.33
syntax =:'()[]{}''`,@'
others =: a.-.spaces,syntax,'"'
digits =: chspan'09'
'LP RP LB RB LC RC Q QQ UQ AT'=: s:;/syntax  NB. names for boxed tokens

nxch =: verb define
  NB. (private) return next character from s and increment cp
  cp=:cp+1 if. cp<ep do. ch=:cp{s else. ch=:0{a. end.
)

nxtok=: verb define
  NB. (private) next s-expr token from s, starting at index cp
  NB. spec:  cp′ = cp + #tok′ ...
  tok=.''
  NB. skip whitespace
  while. (ch e. spaces) *. (cp < ep) do. nxch'' end.
  if. cp < ep do.
    NB. single char tokens become boxed symbols
    if. ch e. syntax do. nxch tok=.s:<ch
    NB. strings (double quoted, with \" allowed) remain literals
    elseif. ch = '"' do.
      while. ((nxch'') ~: '"') *. (cp < ep) do.
        if. ch='\' do. tok=.tok,nxch'' else. tok=.tok,ch end.
      end.
      nxch'' NB. drop trailing '"'
    NB. anything else is a number or a symbol
    elseif. do.
      while. (ch e. others) *. (cp<ep) do. nxch tok=.tok,ch end.
      if. *./tok e. digits do. tok=.".tok else. tok=.s:<tok end.
    end.
  else. ok end.
  <tok return. NB. the boxed token.
)

tokens=: verb define
  NB. treat string y as s-expr and return boxed tokens
  ep =: # s=:y
  if. ep=0 do. y
  else. NB. spec: cp′=#s
    ch =: (cp=:0) { s=:y [ r=:''
    while. cp < ep do. r=:r,nxtok'' end.
  end.
)

NB. s-expression parser

parse =: verb define
  if. # toks =. tokens y do.
    bx =. a: conew 'Boxer'
    try.
      for_tok. toks do.
        select. >tok
        case. LP do. pushstate__bx 0
        case. RP do. popstate__bx''
        case.    do. append__bx tok
        end.
      end.
      (r=.result__bx'') [ destroy__bx''
    catch.
      destroy__bx''
      'malformed s-expression' throw.
    end.
  else. r=.>a: end.
  r return.
)

NB. dtw = delete trailing whitespace (like dtb, but with newlines, etc)
dtw =: #~ ([: +./\. 32 < 3&u:)
sx_z_ =: parse_sx_@dtw_sx_


NB. mini test suite
a =: [: assert ]

a        a: = sx ''
a      (<1) = sx '1'
a     (1;2) = sx '1 2'

NB.  fix memory leak here!
verb :0 ''
  goterr=.0 try. sx ')...' catch. goterr=.1 end.
  a goterr
)

NB. ok, now let''s parse a valid s-expression:
cheq sx '1 ( 2(3 4 5  ) 6) 7'
┌─┬─────────────┬─┐
│1│┌─┬───────┬─┐│7│
│ ││2│┌─┬─┬─┐│6││ │
│ ││ ││3│4│5││ ││ │
│ ││ │└─┴─┴─┘│ ││ │
│ │└─┴───────┴─┘│ │
└─┴─────────────┴─┘
)

cheq sx' () (()) (() (())) '
┌──┬────┬─────────┐
│┌┐│┌──┐│┌──┬────┐│
│││││┌┐│││┌┐│┌──┐││
│└┘│││││││││││┌┐│││
│  ││└┘│││└┘│││││││
│  │└──┘││  ││└┘│││
│  │    ││  │└──┘││
│  │    │└──┴────┘│
└──┴────┴─────────┘
)
