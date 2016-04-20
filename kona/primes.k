/ ( this file is currently just rough experimental junk )

/ the idea is to create a prime number generator
/ it would combine an array of numbers that tracks the gaps between candidates..

/ for example, since you know that 2 is the only even prime, you
/ can start with 3 and only consider odd numbers when you test for primality.
/ this cuts the search space in half. By extending this just to the first five primes,
/ you eliminate about 80% of the work... but how do you count by 2 3 5 7 11 ? 

/ here's one way:

ev:{0,(x-1)#1}                   / 0 every n bits...  ev 3 -> 0 1 1  (use # to repeat)

/   ev' 2 3 5
/ (0 1
/  0 1 1
/  0 1 1 1 1)

/ We need to repeat these patterns, and then make a block long enough that all three patterns
/ stay in sync. Since the numbers are prime, we need to multiply them together, and extend
/ the pattern to length 30.

/   (*/2 3 5) #'  ev' 2 3 5
/ (0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1
/  0 1 1 0 1 1 0 1 1 0 1 1 0 1 1 0 1 1 0 1 1 0 1 1 0 1 1 0 1 1
/  0 1 1 1 1 0 1 1 1 1 0 1 1 1 1 0 1 1 1 1 0 1 1 1 1 0 1 1 1 1)

/ ANDing these rows together gives us a bit vector where the 0s are multiples
/ of a known prime, and therefore can be ignored:

/  &/ (*/2 3 5) #'  ev' 2 3 5
/ 0 1 0 0 0 0 0 1 0 0 0 1 0 1 0 0 0 1 0 1 0 0 0 1 0 0 0 0 0 1

/ Monadic & can then find the indices of the 1 bits, and we can test these for primality:

/  &&/ (*/2 3 5) #'  ev' 2 3 5
/ 1 7 11 13 17 19 23 29

/ as it happens, all of these results are prime except for 1. 
/  &&/ (*/2 3 5) #'  ev' 2 3 5

/ however, we can keep adding these numbers to multiples of 30 to test more blocks:

/   30 + 1 7 11 13 17 19 23 29
/ 31 37 41 43 47 49 53 59

/ here, the first number actually is prime. (they all are, except 49, which is 7x7).
/ If we had added 7 to our initial list, we would have increased the block size by 7
/ but would have to increase the block size to 30 * 7, which is 210.

/ the more primes we add to the sieve, the fewer we have to actually consider.

/ since the list will contain false positives, we still need to actually
/ peform a test to see whether or not they are prime.
/ For natural numbers x and k, when x is prime, ((x^k) mod k) = x, so 
/ before we loop through and try check a bunch of primes to see whether
/ or not they may be factors, we could try:
/   {[n;k] k {(x*n)!k}/1 }[ 3; 5 ]
/ 3

/ If we stumble on a number where the result is not the same as n, we know that
/ k is not prime. However, there are composite numbers for which all values of
/ (n^k)mod k  == k. These are called Carmichael numbers and the first is 561.
/  (!561) ~ {[n;k] k {(x*n)!k}/1 }[!561; 561 ]
/ 1

/ Also, checking even one of these is an O(n) operation (with the algorithm above),
/ making a thourough check O(n*k). But since the thourough check might hit a Carmichael
/ number and a simple division test can be done just by checking the primes up to sqrt(k),
/ this technique doesn't really buy us much.

/ If we had support for arbitrarily large numbers, then we could do 2^n as a single
/ shift operation on a vector of n bits. (1 followed by n 0s is 2^n in binary). This
/ would let us perform a single division as a quick check before moving on to some
/ better test.

/ However, (AFAIK) kona doesn't have a big integer library, so if I were to do this,
/ I might implement https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test


/ i don't have time to do this now though, so here's some junk code i made while
/ thinking this through. :)


/ sieve of the first few primes 
p: 2 3 5 7 11                    / initial set of known primes
k: */p                           / block size
b: & &/ k #' ev'a                / possible primes in the block (about 20% of full block)
g: -': b                         / gaps between those numbers


k: 2; p: 2; a:,2      / n: last known; p: product of primes; a: answer
s: 0 1                / initial sieve

a2s:{1 _,/" ",'$x}       / array 2 string
n:0
while[n<2;n+:1
  c: k + &s               / generate n candidates, starting at k
  `0: "c: ",(a2s c),"\n"
  while[#c
    k: *c; a: a,k; p:p * k  / first item is guaranteed to be prime
    s: &/ p #'(s; ~ ev k)
    c: 1 _ c; ] ]


/   by2: 0 1 0 1 0 1
/   by3: 0 0 1 0 0 1
/   (,3+!6),,by2|by3
/ (3 4 5 6 7 8
/  0 1 1 1 0 1)

/ prototypes in j:

/ J:
/ # 2 -~/\ I. *./ (*/y) $ S:0 (0, <: $ 1:) L:0 ;/ y=:2 3 5 7 11
/ 12 4 2 4 6 2 6 4 2 4 6 6 2 6 4 2 6 4 6 8 4 2 4 2 4 14 4 6 2 10 2 6 6 4 2 4 6 2 10 2 4 2 12 10 2 4 2 4 6 2 6 4 6 6 6 2 6 4 2 6 4 6 8 4 2 4 6 8 6 10 2 4 6 2 6 6 4 2 4 6 2 6 4 2 6 10 2 10 2 4 2 4 6 8 4 2 4 12 2 6 4 2 6 4 6 12 2 4 2 4 8 6 4 6 2 4 6 2 6 10 2 4 ...
/    +/\ 1, 2 -~/\ I. *./ (*/y) $ S:0 (0, <: $ 1:) L:0 ;/ y=:2 3 5 7 11
/ 1 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163 167 169 173 179 181 191 193 197 199 211 221 223 227 229 233 239 241 247 251 257 263 269 271 277 281 283 289 293 299 307 311 313 317 323 331 33...


/ here's (2^k)mod k as a primality test in j. it finds all primes, but hits a false positive at 341.
/ (-:p:@i.@#) 2,I.2=(|2^])i.341x
