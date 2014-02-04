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

  usage:        if u then (v else w) y
  means:    ] f ^:([: -. [: +: [: -. (v :. w))"0 y

In this version, both 'then' and 'else' are
conjunctions, while 'if' is simply the ']' verb.

The resulting verb train is a monadic rank 0 hook.
In dyadic context, it simply ignores its left
argument.

The '(v else w)' part requires parentheses, but
the phrase as a whole does not.

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

