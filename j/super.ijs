NB. test of inheritance

coclass<'SuperClass'
create =: ]
method =: +:

----------------------------------------------------------------

coclass<'SubClass'
coinsert 'SuperClass'
method =: [: >: method_SuperClass_

----------------------------------------------------------------

cocurrent 'base'
sup =: conew 'SuperClass'
sub =: conew 'SubClass'

assert 0 2 4 6 8 = method__sup i.5
assert 1 3 5 7 9 = method__sub i.5
