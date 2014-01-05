load'debug'
dbr 1

in =: e.

txt=: 'A=X,B. B=AC. C=[A].'

cp =: 0
ch =: ''
sym=: ''
atoz =: 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
NUL =: 0{a.
EOF =: 4{a.
error=: 3 : 0
  echo'error. halting.'
  exit''
)

expect=:3 : 0
  if. sym -: y do. getsym''
  else.
    echo 'error: expected "', y, '" but got ', sym
    exit''
  end.
)

eof =: verb : 0
  cp >: # txt
)

getsym =: verb : 0
  whilst. ch -: ' ' do.
    if. cp < # txt do.
      sym =: cp { txt
      cp  =: cp + 1
      stdout sym
    else.
      sym =: EOF
    end.
  end.
)

production =: verb : 0
  getsym''
  if. sym in atoz do. getsym'' else. error'' end.
  expect'='
  expression''
  expect'.'
)

factor =: verb : 0
  if. sym in atoz do. getsym''
  elseif. sym -: '[' do.
    getsym''
    term''
    expect']'
  elseif. 1 do. error'' end.
)

term =: verb : 0
  factor''
  while. sym in atoz,'[' do. factor'' end.
)

expression =: verb : 0
  term''
  while. sym = ',' do.
    getsym''
    term''
  end.
)

main =: verb : 0
  while. -. eof'' do.
    production''
  end.
)

main''
