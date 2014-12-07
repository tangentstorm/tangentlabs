NB. 1215.2013

NB. absalom posed a question to his students
NB. about generating the following sequence:

       1
     121
   12321
 1234321
     ...

NB. he asked us if he could make it shorter:
NB. a = absalom  t = tangentstorm  f = fftw




a0 =: (,&1)$(*:@:(%&9)@:<:@:(10x&^)@:>:@:i.)
t0 =: (3 :',.*:10x p.~(i.y)#"0[1')

NB. f0 is shortest but it generates a 0 up front and factors out the i.

f0 =: (3 :'*: ". y # ''1'''"0)

f0 =: (3 :'*:".y#''1'''"0) NB. without spaces
t1 =: (3 :',.*:+/\10x^i.y')

NB. j = jpjacobs:
j0 =: ,.@:(*:@".@(#&'1')@>:) i.5


NB. b = b_jonas
b0 =: ":*:<.9%~<:10^9

NB. this one is cute but only works up to 9
NB. because it uses ascii digits
   t2 =: (,|.@}:)\(a.{~49+i.)  
   t2 9
1
121
12321
1234321
123454321
12345654321
1234567654321
123456787654321
12345678987654321
