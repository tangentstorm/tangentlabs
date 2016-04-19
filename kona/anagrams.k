/ port of j's A. verb (anagram/anagram index) to kona

del:{(y#x),(y+1)_ x}                          / delete yth item from x

ana:{ / -> xth permutation of array y
  n:#y; s:!n; a:()                            / n:numslots, s:slotnums, a:answer
  while[n>0
    r: x ! n; x: x % n; n: n-1                / divmod
    a: a,s@r; s: del[s;r]]		      / select next slot based on remainder
  y@a}

aix:{ / anagram index. x should be some permutation of !#x
  / this treats x as digits of a number in a factorial base.
  / the leftmost digit needs to be multiplied by fac[n-1]
  / then the other digits are renumbered. eg:
  /     aix 2 1 0 3 = (2 * fac 3) + aix 1 0 2
  /                 = (2 * fac 3) + (1 * fac 2) + aix   0 1
  /                 = (2 * fac 3) + (1 * fac 2) + (0 * fac 1)
  /                 = 12 + 2
  /                 = 14
  n: #x; a:0
  while[n>0
    a: (*x) + a * n                          / implicit factorial  
    x: < 1 _ x                               / re-number the remaining digits
    n: n-1 ]
  a}

t: "0 1 0 1 2 3 4 5 23 ~ aix' (0 1; 1 0; 0 1 2; 0 2 1; 1 0 2; 1 2 0; 2 0 1; 2 1 0; 3 2 1 0)"
if[~. t; `0:"failed:",t]
