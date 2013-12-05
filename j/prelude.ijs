zip =: dyad : 0
  n =. ($y)<.($x)
  try.
    r =. (n$y)(,"0)(n$x)
  catch.
    r =. (n$y)(;"0)(n$x)
  end.
  r
)
