NB. a logic library for j

NB. basic vocabulary for doing logic:
NB. ------------------------------------------------------


NB. one line logic library:
('p q' =: |:#:,.i.2^2)[('`not and or xor nor nand imp nim reverse' =: -.`*.`+.`~:`+:`*:`<:`>`|.)
assert (p nand q) = reverse not (p nor q)
assert (p and q) = reverse not (p or q)


'F T' =: 0 1

A  =: and =: [: : *.    NB. dyadic +: is logical and
V  =: or  =: [: : +.    NB. dyadic +. is logical or
X  =: xor =: [: : ~:    NB. dyadic ~: is logical xor
is =: iff =: [: : =
N  =: not =: -. : [:    NB. monadic -. is 'logical not'
c  =: chk =: [: -. 0 e.]    NB. c y = not(y contains 0)

imp =: [: : <:    NB. dyadic <: is implication  (so is !)
iby =: [: : >:    NB. dyadic >: is 'implied by'

NB. if.a do.b else.c end. <--> ite a,b,c (bools only)
ite =: 0 1 0 1 0 0 1 1 {~ #.

NB. truth variables ( p q r s t )
NB. ------------------------------------------------------
NB. These are the transposed bits of the numbers [0..31]
NB. this lets us test all combinations of 5 different
NB. input bits simultaneously.

bitvars =: adverb : '|: #: ,. i. 2^m'
'p q r s t' =: 5 bitvars

pp =: 'FT' {~ ]        NB. pretty print ('FT' for 0 1)
jj =: pp inv           NB. inverse of pp
tt =: adverb :'u"0/~ 0 1'  NB. shows a pretty truth table

NB. -------------------------------------------------
NB. some examples
NB. -------------------------------------------------
a =. assert"0

NB. identity
a   p = p V 0
a   p = p A 1

NB. Null
a   1 = p V 1
a   0 = p A 0

NB. Idempotency:
a   p = p V p
a   p = p A p

NB. Involution:
a   p = -. -.p

NB. Inverse:
a   1 = p V -. p
a   0 = p A -. p

NB. Commutative:
a  (p V q) = (q V p)
a  (p A q) = (q A p)

NB. Associativity
a  ((p V q) V r) = (p V (q V r))
a  ((p A q) A r) = (p A (q A r))

NB. Distributivite:
a   (p A (q V r)) = (p A q) V (p A r)
a   (p V (q A r)) = (p V q) A (p V r)

NB. Uniting:
a   p = (p A q) V (p A -.q)
a   p = (p V q) A (p V -.q)

NB. Absorption:
a   p = p V (p A q)
a   p = p A (p V q)

a   ((p V -.q) A q) = (p A q)
a   ((p A -.q) V q) = (p V q)

a   (p >: q) <: (p >: p A q)  NB. deduce (p imp p A q) from (p imp q)


NB. Factoring:
a   ((p V q) A r V -.p) = ((p A r) V (q A -.p))
a   ((p A q) V r A -.p) = ((p V r) A (q V -.p))

NB. Consensus:
a   ((p A q) V (q A r) V (r A -.p)) = (p A q) V (r A -.p)
a   ((p V q) A (q V r) A (r V -.p)) = (p V q) A (r V -.p)

NB. de Morgan''s:
a   (-. p V q V r V s) = (-.p) A (-.q) A (-.r) A (-.s)
a   (-. p A q A r A s) = (-.p) V (-.q) V (-.r) V (-.s)

NB. de morgan simplified for j:
a   (A/-.p,q,r,s) = (-.V/p,q,r,s)
a   (V/-.p,q,r,s) = (-.A/p,q,r,s)

a (-.@A = V&-.)~ p,q,r,s
a (-.@V = A&-.)~ p,q,r,s


NB. words that check properties of logical operators.
NB. ---------------------------------------------------

isReflexive =: adverb : 0
  (0 u 0) *. (1 u 1)
)

isAssociative =: adverb : 0
  'P Q R' =. 3 bitvars
  ((P u Q) u R) -: (P u (Q u R))
)

isCommutative =: adverb : 0
  'P Q' =. 2 bitvars
  P (u -: u~) Q
)

distsOver =: conjunction : 0
  'P Q R' =.3 bitvars
  (P u (Q v R)) -: ((P u Q) v (P u R))
)


a     = isReflexive
a    <: isReflexive

a     >: isReflexive
a  -. >: isCommutative
a     >: isReflexive
a  -. >: isCommutative

a     +. distsOver *.
a     *. distsOver +.


NB. solver
NB. ----------------------------------------
NB.   usage: (vars) given (facts)
NB. example:  1 = q given p, p imp q

given =: ,@([: _:^:(2=#)@ ~."1  [ #"1~ *./@])

a   (, 1) -: p given p
a   (, _) -: q given p
a   (, 1) -: q given p, p imp q
a    1 1  -: (p,q) given p, p imp q



NB. shannon expansion
NB. this should always produce an dentical function so
NB. I am not entirely sure what the value is here.
shannex =: adverb : '((u 1) and y) or ((u 0) and not y)'
