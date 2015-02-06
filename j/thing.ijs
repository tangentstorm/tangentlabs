echo cls

bp =: [ , -:@+ , ]  NB. from earlier
even =: (>0:) *. (0=2|])
nbits =: [: >. 2 ^. ]
drop2 =: verb define
  if. 1 > n=. +/2=y do. echo 'y must contain a 2 (got:',(":y),')' throw. end.
  \:~ (2#~n-1), y-.2 return.
)

status =: verb define
  'lob mid hib lo m hi s i'=.y
  ss =. 2 ^ s [ t=.i<:m
  msg=.('lo m hi=',":lo;m;hi);('(',(":i),'<:m):',(":t));'ss=2^',(":s)
  echo msg ,('m=',":m); 'bounds:',":lob;mid;hib
)

factor =: verb define
  f =. >a: if. y < 0 do. y=. -y [ f =. _1, f end.
  while. even y do. 'f y' =. (f,2); -:y end.
  if. y e. 0 1 2 do. 1 -.~ f, y return. end.
  i =. y [ lo =. 1 [ m =. _. [ hi=. 2 [ s =.  <: nbits y
  while. s>:0 do.
    gap0 =. (*/hi,s)-(*/lo,s)
    t =. i <: 'lob mid hib'=.(2^s) * ('l m h'=. ((*/lo) bp (*/hi)))
    status lob;mid;hib;lo;m;hi;s;i
    assert m <: lob
    assert hib >: m
    hi=.hi,2 [ lo=.lo,2 [ s=.<:s
    NB. if. m = 0.5+<.m do. hi=.hi,2 [ lo=.lo,2 [ s=.<:s end.
    if. t do. hi=. m meld hi [ echo (":i),' <: ',(":mid),', so mid->hi'
    else. lo=. m meld lo     [ echo (":i),' > ',(":mid),', so lo<-mid' end.
    gap1 =. (*/hi,s)-(*/lo,s)
    if. gap1 >: gap0 do. echo 'error: gap should have shrunk.' throw. end.
  end.
  if. t do. r=.lo else. r=.hi end.
  f,r-.1 2 return.
)

meld =: dyad define
  echo (":x),' meld ', (":y)
      if.(<.x) = x     do. x=.<.x
  elseif.(<.x) = x-0.5 do. x=.2*x [ y=.drop2 y
  elseif. do. echo'invalid x' throw. end.
  echo '->', ": res =. \:~ 1-.~x,y
  res return.
)

echo'factoring 27:'
(q:;factor) 27
