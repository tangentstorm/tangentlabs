load 'logic.ijs'
load 'irctoys.ijs'
'`VO RU NA TI' =: (]"0)`(0:"0)`(-."0)`(1:"0)  NB.


NB. should we start with 0? 1? 0{y?
NB. usage: vo`vo apv0 0

'vo ru na ti'=: 0 0, 0 1, 1 1,:,: 1 0         NB. masks for xor scan
apv0 =: dyad def ('~:/ 0,     (,y) }|: x') "_ 1
apv1 =: dyad def ('~:/ 1,     (,y) }|: x') "_ 1
apv  =: dyad def ('~:/ ({.y), (,y) }|: x') "_ 1

NB. rollcall. show
rollcall =: (16$:]) : (i.@[ (2 2 $'missing:';-.;'found:';[-.-.) ])
rollbits =: rollcall@(#.S:0)

bpair =: [: |: (<.,>.@(1|])) "0  NB. converts 0.1 → 0 1, etc.
vord  =: (vorop bpair@])~ "_ 1   NB. matrix on left, input on right


NB. we build a machine out of 4 operators:
NB. usage: (e`f`f`h mkm) <==> (e/ . ((f{.) g (h{:)))
mkm =: adverb define
  '`e f g h'=.u
  (e/ . ((f{.) g (h{:)) f.)
)

NB. search the space:
NB. there are 8 bits in a 3->1 bit truth table,
NB. so there must be 256 such functions. But two 3x1 matrices
NB. only distinguish 64 (2^3*2)... so we must need an extra 1
NB. bit at the end and an extra bit in each matrix,
NB. so we have some kind of binary affine transformation.
answers3  =: adverb : '(#:i.8) ((1,.[) u"1 2/ ]) 2 4 $"1 (#:i.256)'
answers   =: adverb : '(#:i.4) ((1,.[) u"1 2/ ]) 2 3 $"1 (#:i.64)'
distinct =: verb : '# ~. #. |:y'

NB. sadly, even with this in place, my first try came up short:
vorop0 =. ~:/ . ((<{.) ~: (*.{:))
assert 16 = distinct vorop0 answers

ops=: 0:`*.`>`[`<`]`~:`+.`+:`=`(-.@])`>:`(-.@[)`<:`*:`1:

maj=:(+/>:-:@#)"1
tv  =: 1 : '(] u [: #: [: i.2^#@])y'  NB. apv tv vo`vo → 0 0 1 1

shv=: 1 : 0
 r=.2 0$0{a.
 for_bits. #:i.4
 do. r=.r,.(2 3$' | '),.blit>(bits u~ ])@:; L:1 { 2$<vo;ru;na;ti end.
)

lyr =: adverb define
 'e f g h'=.u
 (e/ . ((f{.) g (h{:)) f.)
)

Note 'apv0 shv ,. apv1 shv'
|  █ | ▐▌ | ▄▀ | ▞▚ | █  | ▌▐ | ▀▄ | ▚▞
| █  | ▌▐ | ▀▄ | ▚▞ |  █ | ▐▌ | ▄▀ | ▞▚
)

Note (1 1 apv1~ ])@:; L:1 { 2$<vo;ru;na;ti
┌─┬─┬─┬─┐
│1│0│0│1│
├─┼─┼─┼─┤
│0│1│1│0│
├─┼─┼─┼─┤
│0│1│1│0│
├─┼─┼─┼─┤
│1│0│0│1│
└─┴─┴─┴─┘

bip =: ~:/ .*.
eqv =: dyad define
  x apv #:i.#,y
)


Note ~., (apv tv)@:; L:1 { 2$<vo;ru;na;ti
┌───────┬───────┬───────┬───────┬───────┬───────┬───────┬───────┐
│0 0 1 1│0 1 1 0│1 1 0 0│1 0 0 1│0 0 0 0│0 1 0 1│1 1 1 1│1 0 1 0│
└───────┴───────┴───────┴───────┴───────┴───────┴───────┴───────┘
)

Note rollbits ~., (apv0 tv)@:; L:1 { 2$<vo;ru;na;ti
┌────────┬──────────────────┐
│missing:│1 2 4 7 8 11 13 14│
├────────┼──────────────────┤
│found:  │0 3 5 6 9 10 12 15│
└────────┴──────────────────┘
)

pairs =: _2&(]\)
pairs vo`ru, na`ti





NB. it turns out there just plain is no universal matrix
NB. composition, even if you allow two different operations.
NB. i suspect this is related to the limits of perceptions.
NB. this tries a multi-layer approach:
mk2 =: adverb define
 '`e f g h'=.u
 ({.@] (e/ .f)~ ((g/ .h){:)) f.
)
count=: adverb def 'distinct u answers'
search =: verb define
 r=:0$0
 for_ger. ((16 #.^:_1 i.16^4) { ops)
 do. r=:r,ger mk2 count end.
)


