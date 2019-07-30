R =: -:^:(-.@(2&|))^:_
S =: 1 + 3&*
T =: R@([`S@.(2&|))"0

C =: T^:(~:1:)^:a:"0 M.

C i. 10

strip0 =: }.^:(0={.)
base =: 2 : 'strip0 n #.^:_1 y'
 ;/"2 [base 3r2 every] ([:<],.S) 1+2*i.10

b32 =: '`', 'o21' {~ 2 * -base 3r2
b6  =: ':', 'o12345' {~ -base 6

bx =: b32"0
i  =: 1+2*i.24
bi =: bx i
b2 =: bx i * 2
b3 =: bx i * 3
bs =: bx S i
bt =: bx T i
I =: ' | '&,"1 
h =: ;:' i bi b2 b3 bs bt T'

[ h,: ,(":"0 i) ;,. bi ;,. b2 ;,. b3 ;,. bs ;,. bt ;,.":"0 T i

,.[base 3r2"0 each ;/ (1+])^:(<10)0

(,.i);(,.3r2^.i);(,.(#@b32@S)"0 i);bi
cnj =: conjunction
apa =: cnj : '(<u n {:: y) (<n) } y '  NB. apply at

((<@b6"0)@*)/~ i.12

T i

load 'plot'
([:pd@>@{:])\ ('reset';'type marker';(T i);'show')

NB. this next line shows how the odd numbers
NB. break into three main groups, based on the
NB. number mod 8. (
viewmat (|.n,x%n) $ T >:+:i.x=.6^5 [ n=.4
(2*n)| {. (|.n,x%n) $ >:+:i.x=.6^5 [ n=.4

NB. actually, mod 16 seems even more interesting.
NB. this seems to work for any m:
(m$s) -: 10{|: (|.n,m) $ s =: T >:+:i.m * n =. 16 [ m =. 500

NB. why does this relation hold?
x =. i.900
(T >: +: x) -: T >: +: 10+ 16 * x  NB. observed. why?
(T >: +: x) -: T >: 20+ +: 16 * x  NB. move +: right
(T 1+ 2* x) -: T 1+ 20+ 2* 16 * x  NB. explicit >: +:
(T 1+ 2* x) -: T 21 + 32 * x 

(T 1+ 2* x) -: T 1+ (4*c)+ (2^c) * x [ c =. 5 NB. maybe?
(T 1+ 2* x) -: T 1+ (4*c)+ (2^c) * x [ c =. 6 NB. nope.

(T 1+ 2* x) -: T 1+ (5*c) + (2*c^2) * x [ c =. 4 NB. or this?
(T 1+ 2* x) -: T 1+ (5*c) + (2*c^2) * x [ c =. 2 NB. nope


NB. curious that the two sequences are the same mod 5
5 | ((1 + 2 * i.),:(21 + 32 * i.)) 100

NB. aha. what if we switch to S?
(S    1+2* x) -: 16 %~ S    21 + 32 * x  NB.1
(1+3* 1+2* x) -: 16 %~ 1+3* 21 + 32 * x  NB.explicit S
(1+   3+6* x) -: 16 %~ 1+   63 + 96 * x
(4 + 6 * x) -: 16 %~ 64 + 96 * x


NB. so why doesn't this show up everywhere?
(4 + 6 * x) -: w %~ (w * 4 + 6) * x [ w =. 7
I. 1 = T >:+:i. 1000
F =: 3 : 'T >:+:i.10,y'
f =: 3 : '(|: i. h${.) T >:+:i.(h =. 10),y'
g =: (>f"0)
h+I. g h+i.100  NB. 16 64 ... extending to 1000 adds 256
