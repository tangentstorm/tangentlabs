NB. a simple key-value dictionary system for j

NB. symbol constructor (for string keys)
sym=:(' '$:]) : (s:@:,)
S=: 1 : 's:'' '',m'

NB. constructors:
emptyd =: a:,a:

NB. x:K map y:V → D(K,V)
dict =: ,&<&, [ ('key/val lengths must match' assert =&#)

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

NB. unicode box chars. (j magically translates these to unicode for display)
uboxch=: [: (9!:7) (a.{~16 17 18 19 20 21 22 23 24 25 26)"_
NB. the same translation as a dictionary, so we can compare to unicode strings.
a2uboxd=:(16 26 17 18 25 22 23 24 dict 9484 9472 9516 9488 9474 9492 9524 9496)
NB. function to apply the map to ascii string y, but leave other chars unchanged:
a2ubox=: (a2uboxd get ::] ])&.(3 u:])"0

lines =: [: (<;._2) 7 u: ]
shouldbe =: [: assert (>@lines@[) -: a2ubox@]

(0 : 0) shouldbe ": ((sym 'a b c') dict ('apple';'banana';'cherry')) get sym 'b a'
┌──────┬─────┐
│banana│apple│
└──────┴─────┘
)

NB. for a version of this that doesn't require dicts, see 'cheq.ijs''


NB. rev y:D → D  (reverse keys and values)
rev =: (}.,{.) : [:

NB. TODO: m:K ins n:V y:Dict → Dict
NB. (adding multiple values for keys)
NB. ins =: 2 : ' '
