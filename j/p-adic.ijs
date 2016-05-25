NB. p-adic numbers in j
NB.
NB. for "what the heck are p-adic numbers?" see these links:
NB. --------------------------------------------------------
NB. https://www.youtube.com/watch?v=XXRwlo_MHnI (great!)
NB. https://www.youtube.com/watch?v=vdjYiU6skgE
NB. http://mathforum.org/library/drmath/view/65286.html
NB. http://www.asiapacific-mathnews.com/03/0304/0001_0006.pdf

adabs0 =: (4 : 0)"0
 NB. x-adic absolute value (norm) of y (x should be prime)
 if. y=0 do. 0
 else.if. y < 0 do. x adabs -y
 else. (x:x) ^ -~/ ([:+/x=]) S:0 <@q: 2 x: y
 end.end.
)

NB. same thing, but tacit:
adabs =: (([$:-@])`0:`(x:@[ ^ [: -~/ [: ([: +/ [ = ])S:0 [: <@q: 2 x: ]))@.(1+*@])