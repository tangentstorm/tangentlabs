NB. extra elements problem
NB. --------------------------------------------
NB. we are given two unsorted arrays of integers
NB. one of which is a copy of the other, except
NB. in a different order and with two extra values.
NB. find the two extra values in O(n) time.

NB. specification
NB. ============================================

NB. requirements for begin state
NB. --------------------------------------------
NB. b0. Every element of a0 is also an element of a1.
b0 =: 3 : '*./a0 e. a1'

NB. r1. a1 has 2 more elements than a0
b1 =: 2 = (#a1) - (#a0)

  NB. e0. output variables n and m are elements of a1, but not a0
  assert. *./ n m e. a1             NB. n in a1 and m in a1
  assert. -. +./ n m e. a0          NB. not(n in a0 or m in a0)

  NB. e1. (a0,n,m) and (a1) have the same members.
  assert. (/:~ a0,n,m) -: (/:~ a1)  NB. t0 = list(sorted(a0+[n,m]))
                                    NB. t1 = list(sorted(a1+[n,m]))
                                    NB. t0 == t1
)

NB. implementation
NB. --------------------------------------------
NB. 
(*./a0 e. a1) <:




NB. -- verify ------
require_conditions''
calculate''
ensure_conditions''
