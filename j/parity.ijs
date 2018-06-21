NB. parity logic. (see also langlet.ijs)
NB. load'logic.ijs'

NB. thue-morse sequence (nothing to do with parity. just generates a nice bit string)
thuem =: 13 : '(y $ (,-.)^:(2^.y) 0 1)'

NB. pariton for a sequence of bits.
Par =: 1|.~:/\^:(<@#)

NB. Geniton of size n
Gen =: [: Par 1,<:$0:


NB. Cognitive transform
PCog =: {:"1
Cog =: PCog@Par

NB. Helical transform
PHel=: ~:/@:* |.@=@i.@#
Hel =: PHel@Par

NB. binary inner product
bip =:(~:/ . *.)


NB. laws
chekb=:(1 :'for_v. #:i.y do. assert u v end.')

(Cog -: (|."1 Gen 8) bip ]) chekb 256
(Hel -: (|."2 Gen 8) bip ]) chekb 256
(Cog -: Hel&.|.) chekb 256
(Hel -: Cog&.|.) chekb 256
(] -: Cog^:2) chekb 256
(] -: Hel^:2) chekb 256


NB. symbolic versions (for 3 variables only, so far)
o =: 0 *. l =: 1 +. a [ 'na nb nc' =: -. 'a b c' =: |. 3 bitvars
abc =: c *. ab =: a *.b [ ac =: a *.c [ bc =: b *. c


NB. symt is a literal description of the truth table, with
NB. one entry per 'true' value.
t_abc=:'(a<b<c<1)';'(a>b+.c)';'(a<b>c)';'(a*.b>c)';'(a<b<c)'
t_abc=:t_abc,'(a*.b<c)';'(a<b*.c)';'(*./a,b,c)'
symt =: ('+./', [: }. [: ; ',' ,L:0 t_abc #~ ]) "1

NB. symh is the helical transform, in algebraic normal form (xor-of-ands)
h_abc=:'l';'a';'b';'ab';'c';'ac';'bc';'abc'
symh =: ('~:/', [: }. [: ; ',' ,L:0 h_abc #~ Hel)"1

NB. symc is the cognitive transform: nxor-of-ors (nxor is '=')
NB. you can convert it to xor-of-ors just by toggling inclusion of
NB. 'l' in the list. (in fact the cognitive transform does this,
NB. but the (}:,-.@{:) flips the final bit for brevity.
c_abc=:'(+./a,b,c)';'(b+.c)';'(a+.c)';'c';'(a+.b)';'b';'a';'o'
symc =: ('=/' , [: }. [: ; ',' ,L:0 c_abc #~ [: (}:,-.@{:) Cog)"1

testp=:{.(a*.b)~:(a*.c)*(a*.b)
assert (-:".@symh) testp
assert (-:".@symc) testp
assert (symh testp) -: '~:/ab,abc'
assert (symc testp) -: '=/(+./a,b,c),(b+.c),(a+.c),c,o'
assert (symt testp) -: '+./(a*.b>c)'
