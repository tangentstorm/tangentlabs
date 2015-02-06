
  bp =: [ , -:@+ , ]  NB. from earlier
  even =: (>0:) *. (0=2|])
  nbits =: [: >. 2 ^. ]
  drop2 =: verb define
    if. 1 > n=. +/2=y do. echo 'y must contain a 2 (got:',(":y),')' throw. end.
    \:~ (2#~n-1), y-.2 return.
  )

  factor =: verb define
    f =. >a: if. y < 0 do. y=. -y [ f =. _1, f end.
    while. even y do. 'f y' =. (f,2); -:y end.
    if. y e. 0 1 2 do. 1 -.~ f, y return. end.
    lo =. 2 [ hi=. 2 2 [ s =. <:<: nbits y
    while. s>:0 do.
      t =. y <: ss * m=. ((*/lo) -:@+ (*/hi))  [ ss =. 2 ^ s
      msg=.('lmh=',":lo;m;hi);('f=',":f);('y<:m=',":t);'s=2^',(":s),'=',":ss
      echo msg ,('y:',":y); 'ss*lmh:',":ss * */ S:0 lo;m;hi
      s =. <: s [ hi=.hi,2 [ lo=.lo,2
      if. t do. hi=.drop2 m meld hi else. lo=.drop2 m meld lo end.
    end.
    if. t do. r=.lo else. r=.hi end.
    f,r-.1 2 return.
  )
  (q:;factor) 27

  meld =: dyad define
    echo (":x),' meld ', (":y)
        if.(<.x) = x     do.
    elseif.(<.x) = x-0.5 do.
    elseif. do. echo'invalid x' throw. end.
    echo '->', ": res =. 1-.~(<.x*2), }. \:~ y
    res return.
  )
