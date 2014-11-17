#!/usr/bin/env j

NB. demo showing how to make a simple repl in j.

readln =: [: (1!:01) 1:
donext =: [: (9!:29) 1: [ 9!:27

main =: verb define
  echo ''
  echo 'main loop. type ''bye'' to exit.'
  echo '--------------------------------'
  while. (s:'`bye') ~: s:<input=:readln'' do.
    echo ".input
  end.
  echo '--------------------------------'
  echo 'loop complete. returning to j.'
  NB. or put (  exit'' ) here to exit j.
)

donext 'main _'
