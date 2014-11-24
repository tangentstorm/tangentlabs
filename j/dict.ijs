NB. a simple key-value dictionary system for j

NB. symbol constructor (for string keys)
sym=:(' '$:]) : (s:@:,)
S=: 1 : 's:'' '',m'

NB. constructors:
emptyd =: a:,a:

NB. x:K map y:V → D(K,V)
dict =: ,&< [ ('key/val lengths must match' assert =&#)

NB. keys y:D → K
keys=: >@[/

NB. vals y:D → V
vals=: >@]/

NB. x:D get y:K → V
get =: [: : ((keys@[i.]) { vals@[) f.

NB. x:D idx y:K → int
idx =: [: : (keys i. ]) f.

NB. len y:D → int
len =: [: >0{$L:0

NB. m:K put n:V y:D → Dict  (replacing existing values for keys)
put =: 2 : 0
  'K V'=:y
  if. (i=:K i.m) >: #K do. (K=:K,m) ] (V=:V,n)
  else. V =: n i } V end.
  K dict V
)


NB. test case / example usage:

assert ({:0 :0) -: ((sym 'a b c') dict ('apple';'banana';'cherry')) get sym 'b a'
┌──────┬─────┐
│banana│apple│
└──────┴─────┘
)

NB. rev y:D → D  (reverse keys and values)
rev =: (}.,{.) : [:

NB. TODO: m:K ins n:V y:Dict → Dict
NB. (adding multiple values for keys)
NB. ins =: 2 : ' '
