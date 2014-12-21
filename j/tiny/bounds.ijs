bc =: adverb define
[: NB. bounds check: x n bc y → does y fall between 0{x and 1{x ?
   NB. n is two bits. 1=i{n indicates i{x check is inclusive.
:
   NB. inspired by http://archive.vector.org.uk/art10000710
   NB. Inner Products for Range Tests by Jonathan Barman
   (x + 1 0 ~: m) (</ . <)~"_ _1 y
)
assert 0 0 1 0 0 -: 1 3 (0 0) bc i. 5
assert 0 0 1 1 0 -: 1 3 (0 1) bc i. 5
assert 0 1 1 0 0 -: 1 3 (1 0) bc i. 5
assert 0 1 1 1 0 -: 1 3 (1 1) bc i. 5

ee =: dyad def 'bounds 0 0'
