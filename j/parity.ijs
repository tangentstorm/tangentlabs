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
o =: 0 *. l =: 1 +. a [ 'a b c' =: |. 3 bitvars
h_abc=:'l';'a';'b';'(a*.b)';'c';'(a*.c)';'(b*.c)';'(*./a,b,c)'
c_abc=:'(+./a,b,c)';'(b+.c)';'(a+.c)';'c';'(a+.b)';'b';'a';'o'
symh =: ('~:/', [: }. [: ; ',' ,L:0 h_abc #~ Hel)"1
symc =: ('=/' , [: }. [: ; ',' ,L:0 c_abc #~ [: (}:,-.@{:) Cog)"1

p=.(a*.b)~:(a*.c)*(a*.b)
assert (-:".@symh) p
assert (-:".@symc) p
assert (symh p) -: '~:/(a*.b),(*./a,b,c)'
assert (symc p) -: '=/(+./a,b,c),(b+.c),(a+.c),c,o'
