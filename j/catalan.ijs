
NB. an even number of guys are sitting around the table. each is going to 
NB. shake hands with one other person. they're all going to shake at once,
NB. and they want to do it in such a way that nobody reaches over anybody else.
NB.
NB. or: given 2*n specific points on a circle, how many different ways can you
NB. draw n non-intersecting chords?
NB.
NB. illustration : http://i.imgur.com/Lku28KE.png


NB. my answer: 
f=: 3 :('if. y=0 do. 1 else. +/(*|.)f i.y end.')"0

] f i.12    NB. 1 1 2 5 14 42 132 429 1430 4862 16796 58786

NB. python translation:
NB. f = lambda n : sum(f(i)*f((n-1)-i) for i in range(n)) if n>0 else 1

NB. turns out this is a well known sequence:
NB. http://en.wikipedia.org/wiki/Catalan_number
