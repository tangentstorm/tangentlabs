#!/usr/bin/env j

NB. a nicely formatted truth table for each of the 16 boolean dyads in j

ops =: '0: *. > [ < ] ~: +. +: = -.@] >: -.@[ <: *: 1:'   NB. boolean ops

tt  =: [:".'"0/~0 1 ',~]   NB. truth table
mid =: [: }. }:            NB. crop the first and last item
pad =: (' ',4{.!.' '])"1   NB. pad to 4 spaces, then prepend 1 more space
ppr =: 'o!' {~ ]           NB. pretty print (replace '01' with 'o!' for readability)
fwd =: 1 :'u ;._1'' '',y'  NB. adverb: for each space-delimited word in string y...

echo ([:mid"1 mid)":|:(pad ; [:(pad ppr) tt) S:0 < fwd ops

NB. output:
NB.
NB.  0:  │ *.  │ >   │ [   │ <   │ ]   │ ~:  │ +.  │ +:  │ =   │ -.@]│ >:  │ -.@[│ <:  │ *:  │ 1:
NB. ─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────
NB.  oo  │ oo  │ oo  │ oo  │ o!  │ o!  │ o!  │ o!  │ !o  │ !o  │ !o  │ !o  │ !!  │ !!  │ !!  │ !!
NB.  oo  │ o!  │ !o  │ !!  │ oo  │ o!  │ !o  │ !!  │ oo  │ o!  │ !o  │ !!  │ oo  │ o!  │ !o  │ !!


NB. bonus: convert 4-bit truth table to its j name
nameof =: [: > (< fwd ops) {~ [: #. ]

assert '*.' -: nameof 0 0 0 1
assert '*:' -: nameof 1 1 1 0

exit''
