(0 : 0) NB. syntax experiments
--------------------------------------------------
Adverbs and conjunctions to simulate traditional
flow control keywords in J.
--------------------------------------------------
)
a_z_ =: assert  NB. names in z accessible anywhere



0#[0 : 0]#( cocurrent 'ifThen0' )################0

If / Then / Else  v.0
==================================================

  usage:        if u then (v else w)
  means:    ] (v :. w)^:([: -. [: +: [: -. u)"0

In this version, both 'then' and 'else' are
conjunctions, while 'if' is simply the ']' verb.

The resulting train is a monadic hook operating on
rank 0. It can be used in a dyadic context, but
will simply ignore its left argument.

The '(v else w)' part requires parentheses, but
the phrase as a whole does not.

The core idea here is:

     _1 1 = ([: -. [: +: [: -. ]) 0 1

The word 'then' creates a new verb that applies
this transformation to (u y), and uses the result
to select either the verb to the right of 'then',
or its obverse. The word 'else' is simply an alias
for ':.', which creates a verb that acts like 'v'
but with obverse 'w'.

(Based on an idea by Sam Falvo.)
)
_ [' code ']_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

if =: ]
then =: 2 : 'v^:([: -. [: +: [: -. u)"0'
else =: :.

_ [' test ']_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

a   4 1 0 2 4  -:   if (<0:) then (*: else +:)  i:2
a   4 1 0 2 4  -:  (if (<0:) then (*: else +:)) i:2
a  (if ] then (| else -.)) 1 1 0 0 1 0 1 0
a   if ] then (| else -.)  1 1 0 0 1 0 1 0
