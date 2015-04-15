NB. The Big Dumb Hash Routine
NB.
NB. This was a hashing function I made for vectors after
NB. looking at a bunch of hashing routines online. It
NB. seemed to give a good variety of results interactively,
NB. but it turned out to have too many collisions.

lsh =: 33 b.  NB. left shift.
cut32 =: (16bffffffff (17 b.) ]) NB. keep the sign bit while hashing

NB. Pad small vectors with some prime numbers, and always include
NB. a prime based on the sum of the vector, just for good measure.
primeseed=: ([: p: 5678+ 910|+/), (,[:p:121+334|+/)^:(#<9:)^:_
'lsh=left shift (y<<x)' assert (5 lsh~ i:3) = 0 1 2 5 10 20 40
assert (primeseed i.10) -: 56467 0 1 2 3 4 5 6 7 8 9
assert (primeseed 0) -: 55933 0 673 709 997 967 719 1063 1511 2857

NB. The final hash function
big_max =: 2^20 NB. room for a million entries.
bigdumbhash =: big_max| [: ([: cut32 ] - (_3 lsh[) + (17 lsh[))/ primeseed

NB. a quick tests shows a small probability of collisions:
assert 0.047 -: ((#-#@~.) % #) bigdumbhash"0 i.2000

NB. but as increase the number of inputs, it kept going up.
NB. (tests commented out because they are also rather slow)
NB. assert 0.19 -: ((#-#@~.) % #) bigdumbhash"0 i. 10000
NB. assert 0.36 -: ((#-#@~.) % #) bigdumbhash"0 i.100000

NB. I abandoned my attempt after discovering the crc foreign,
NB. which is both much faster and quite unlikely to collide:
(crc =: 128!:3) (binrep=: 0&(3!:1))
assert 0 -: (#-#@~.) (2^20) | crc binrep i.1000000
