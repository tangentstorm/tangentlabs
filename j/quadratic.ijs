NB. in a different order and with two extra values.
NB. find the two extra values in O(n) time.

NB. Random number setup
NB. ============================================
NB. Set 'rnd =: ?.' to use a fixed seed so that the
NB. generated values are consistent between runs.
NB. Set 'rnd=: ?' to use a random seed.
rnd =: ?.  NB.

NB. specification
NB. ============================================

NB. begin state
NB. --------------------------------------------

NB. b0. Every element of a0 is also an element of a1.
b0 =: 3 : '*./a0 e. a1'

NB. b1. a1 has 2 more elements than a0
b1 =: 3 : '2 = (#a1) - (#a0)'

NB. requirements for end state
NB. --------------------------------------------

NB. e0. output variables n and m are both elements of a1
e0 =: 3 : '*/ (n,m) e. a1'

NB. e2. n and m are what remain after removing one matching
NB.     element from a1 for each element of a0
NB.     We'll demonstrate this by sorting the two lists and
NB.     then
e1 =: 3 : 0
  s0  =. /:~ a0      NB. sorted version of s0
  s1  =. /:~ a1      NB. sorted version of s1
  rv  =. 0$0         NB. result value starts as empty list
  for_i. # s0 do.
    h =: {. s1
    if. h = {. s0 do.
      s0 =. }. s0    NB. heads match, so behead s0
    else.
      rv =: rv,h     NB. s1 is extra, so add to result
    end.
    s1 =. }. s1      NB. behead s1 either way
  end.
  nm =. /:~ n, m     NB. sort (n, m)
  nm -: /:~ rv       NB. sort rv and check for match
)

NB. The above routine produces the correct solution,
NB. but does so in O(n log n) time because the two arrays
NB. are sorted first. The goal solution must be O(n)
NB.
NB. todo : use time/space foreigns to demonstrate O(n) time

NB. rq is just a single verb that checks all requirements:
rq =: b0, b1, e0, e1

NB. verify the results
verify =: 3 : ('echo rq'; 'assert *./ rq _')

NB. implementation
NB. ============================================

NB. setup
NB. ---------------------------------------------

NB. let a0 be some random integers between _100 and 100
] a1 =: _100 + rnd 27 $ 200

NB. let ij hold two random indices into a1
] ij =: 2 rnd # a1

NB. Let t be a1 with the items at indices ij removed
] t =: a1 #~ -. (i. # a1) e. ij

NB. finally, let a0 be some random permutation of t
] a0 =: t A.~ rnd 2^30

NB. the above conditions satisfy b0 and b1.
assert (b0 *. b1)''

NB. calculations
NB. ---------------------------------------------

NB. let nms be the sum of a1 minus the sum of a0
] nms =: (+/a1) - (+/a0)
] nms =: +/a1,-a0                       NB. simplified.

NB. let nms be the product
] nmp =: (*/a1) % x: (*/a0)             NB. x: is extended precision
] nmp =: */a1, % x: a0                  NB. simplified.

NB. we will now solve the problem algebraically.
NB. later, when we've calculated the actual values
NB. for n and m, we can run this routine to verify
NB. that each statement it contains is in fact true.
soluion =: 3 : 0

A =. assert

A      nmp = n * m                       NB. p0. given
A      nms = n + m                       NB. p1. given

A  (m + n) = nms                         NB. p2. ← p1 by dy =
A        m = nms - n                     NB. p3. ← p2 by dy -
A      nmp = n * nms - n                 NB. p4. ← p0 by p3
A      nmp = (nms * n) - n^2             NB. p5. ← p4 by dy * (right to left!)
A        0 = (-nmp) + (nms * n) - n^2    NB. p6. ← p5 by dy -
A        0 = nmp + (-nms * n) + n^2      NB. p7. ← p6 by mo -
A        0 = n p.~ nmp, (-nms), 1        NB. p8. ← p7 by dy p.~

NB. At this point, we have a quadratic equation, represented as an array.
NB. If you're lost, equation p8 above would be (n^2 - nms*n - nmp = 0) in maxima.
NB. The coefficients are ordered 'backwards' from traditional math notation
NB. so that the array index corresponds to the power. Therefore:

A      1234 = 10 p.~ 4 3 2 1                           NB. j0.
A      1234 = 10 ([: +/ ] * [ ^ [: i. [: #) 4 3 2 1    NB. j1. scary j equivalent to p.~
A      1234 = +/ 4 3 2 1 * 10 ^ i. # 4 3 2 1           NB. j2. what it really means
A      1234 = +/ 4 3 2 1 * 10 ^ i. 4                   NB. j3. 4 ← # 4 3 2 1 (length of the array)
A      1234 = +/ 4 3 2 1 * 10 ^ 0 1 2 3                NB. j4. 0 1 2 3  ←  i. 4
A      1234 = +/ 4 3 2 1 * 1 10 100 1000               NB. j5. ← j4 by ^
A      1234 = +/ 4 30 200 1000                         NB. j6. ← j5 by *
A      1234 = 1234                                     NB. j7. ← j6 by +/

NB. At runtime, we will have actual integer values for nmp and nms, so we can
NB. treat them as constants, and can plug them into the quadradtic formula to
NB. solve for n. In fact, the monadic form of p. can solve the polynomials for
NB. us at this point, but let's work through it by hand before we look at that.

NB. The Quadriatic formula
NB. --------------------------------------------
NB. In a more traditional syntax (maxima),
NB. a quadratic equation looks like this:
NB.
NB.      a*x^2 + b*x + c = 0
NB.
NB. and the quadratic formula (which is just the result
NB. of solving the above equation for x) looks like this:
NB.
NB.     x = (-b + sqrt(b^2 - 4*a*c)) / (2*a);
NB.
NB. (the + should be ± but it doesn't really matter)
NB.
NB. Now, let's derive this formula using J syntax.
NB. First, we will plug in our randomly generated data in
NB. order to check each step at runtime. We will continue
NB. to use 'n' for our variable, but adopt the traditional
NB. names for the coefficients:

(a =. x:1) [ (b =. -x:nms) [ (c =. x:nmp)   NB. p9. given

NB. Again, the x: is just telling j to use extended precision
NB. values, so that floating point issues don't mess up division.

A     0 = n p.~ c, b, a                     NB. p10. ← p8 by p9

NB. The line above is the 'proper' j syntax for 'a*x^2 + b*x + c = 0'
NB. and is quite handy for expressing specific polynomial equations,
NB. but we will write the expanded form. (Compare p11..p18 to j0..j7 above)

A   0 = n ([: +/ ] * [ ^ [: i. [: #) c,b,a  NB. p11. ← p10 by definition of p.~ in j1
A   0 = +/ (c,b,a) * n ^ i. # c,b,a         NB. p12. ← p11 by application
A   0 = +/ (c,b,a) * n ^ i. 3               NB. p13. 3 ← # c,b,a
A   0 = +/ (c,b,a) * n ^ 0 1 2              NB. p14. 0 1 2 ← i. 3
A   0 = +/ (c,b,a) * (n^0), (n^1), (n^2)    NB. p15. ← p14 by distribution of n&^
A   0 = +/ (c*n^0), (b*n^1), (a*n^2)        NB. p16. ← p15 by distribution of (c,b,a)&*
A   0 = (c*n^0) + (b*n^1) + (a*n^2)         NB. p17. ← p16 by distribution of +/
NB. --------------------------------------
A   0 = c + (b*n) + a*n^2                   NB. p18. ← p17 by simplification of ^

NB. Now let's derive the quadratic formula.
NB. (roughly following the derivation at http://en.wikipedia.org/wiki/Quadratic_formula )

A                        0 = c + (b*n) + a*n^2                NB. q0. ← p18. (but also just any quadriatic equation)
A                        0 = (c % a) + (b * n % a) + (n^2)    NB. q1. ← q0 by (% & a) (given that a ~: 0)
A                        0 = (c%a) + (b*n%a) + (*:n)          NB. q2. ← q1 by *: (square)
A                (- c % a) = (b * n % a) + (*:n)              NB. q3. ← q2 by subtracting (c % a)
A    ((*: -: b%a) - c % a) = (*: -: b%a) + (b * n%a) + (*:n)  NB. q4. ← q3 ('completing the square')
A    ((*: -: b%a) - c % a) = (*: n + b % +: a)                NB. q6. ← q5 factor the square
A (lhs=.(*: n + b % +: a)) = (*: -:b % a) - (c % a)           NB. q7. ← q6 swap sides to reduce parens
A                    (lhs) = (*: b % +:a) - (c % a)           NB. q8. ← q7 (-:x % y) <--> (x % +:y)
A                    (lhs) = ((*:b)% *:+:a)-(c % a)           NB. q9. ← q8  distribute *:
A                    (lhs) = ((*:b)% *:+:a)-(c * a % *:a)     NB. q10. ← q9 rightmost term * a % a
A                    (lhs) = ((*:b)% *:+:a)-(c*a*4 % 4**:a)   NB. q11. ← q10 rightmost term * 4 % 4
A                    (lhs) = ((*:b)% *:+:a)-(c*a*4 % *:+:a)   NB. q12. ← q11 4**:x <--> *:+:x
A                    (lhs) = ((*:b) - c*a*4) % (*:+:a)        NB. q13. ← q12 factor out %(*:+:a)
A        (*: n + b % +: a) = ((*:b) - c*a*4) % (*:+:a)        NB. q14. ← q7 restore lhs

                       pm =. (+,-)  NB. ± operator
A             1 _1 =   pm 1         NB. monadic sense
A             6  4 = 5 pm 1         NB. dyadic sense

A           (n + b % +: a) = ((+,-) %:(*:b)-c*a*4) % +:a      NB. q15. ← q14 %: (sqrt) of both sides
A                       n  = (-b (+,-) %:(*:b)-c*a*4) % +:a   NB. q14. ← q13 by (- b % +: a)
NB. ----------------------------------------------------------
A               n  = (b (+,-) %: (*:b)-c*a*4) % +:a

)

qf =: 3 : 0  NB. the quadratic formula
  'c b a' =. y'
  (b (+,-) %: (*:b)-c*a*4) % +:a'
)

NB. todo: now plug in the values and solve the original problem :)

NB. verification
NB. ---------------------------------------------
verify''
derivation''
