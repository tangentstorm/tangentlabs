NB. http://www.jsoftware.com/docs/help701/primer/basic_list_adding.htm

addlists =: dyad : 0
  r =. ''
  count =. # x
  i =. 0
  while. i < count do.
    left =. i { x
    right =. i { y
    sum =. left + right
    r =. r, sum
    i =. i + 1
  end.
  r
)


adda =: dyad : 0
  r =. ''
  count =. # x
  i =. 0
  while. i < count do.
    r =. r, (i { x) + (i { y)
    i =. i + 1
  end.
  r
)
